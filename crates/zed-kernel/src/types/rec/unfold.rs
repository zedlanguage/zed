//! The unfolding of a recursive type: the units of work that keep and free its instances'
//! members, and the evaluation and naming of a definition's body at its arguments.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock, PoisonError, Weak};

use super::{At, Def, Env, Key, Node, Shape, same};
use crate::types::{self, Piece, Rope, TextClass as Class, TextPlace as Place, Type};

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
    UNIT.with_borrow(|u| u.number)
}

/// The number of this thread ([`Unit::thread`]).
pub(super) fn thread() -> u64 {
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
            name_digest: 0,
            args,
            members: Vec::new(),
            judged: OnceLock::new(),
            diagonal_empty: OnceLock::new(),
            part_names: Mutex::default(),
            nodes: Mutex::default(),
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
    /// in a unit, or the one still held from an earlier unit ([`Env::node`]), and kept, by the
    /// instance, until the unit ends. Another thread that made it at the same time may have
    /// kept its own first, which is then the one.
    fn member(self: &Arc<Env>, i: usize) -> Type {
        if let Some(t) = &*self.cell(i) {
            return t.clone();
        }
        // A plain member is set when the instance is made, so this one is recursive.
        let made = self.node(At::Member(i), || {
            let (e, named) = (self.clone(), self.clone());
            Type::rec(
                Key::new(self.clone(), At::Member(i)),
                move || named.name(i),
                move || eval(&e.group().0.bodies[i], &e),
            )
        });
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

    /// The node of the recursive member or part at `at`: the one still held, by anyone, or else
    /// `make()`, kept weakly as the node of `at`. Since every node of `at` unfolds to the same
    /// type, one node per place while it is held keeps a type printed the same however often
    /// its unfoldings were forgotten: before, a member held past the end of its unit (`R` held
    /// `R0` in `R = R0 \ Never`) and the one made again in its cycle were two nodes, which the
    /// printer, keying a diagram by the nodes in its rows, wrote apart, with one definition
    /// fewer than in the first print.
    fn node(&self, at: At, make: impl FnOnce() -> Type) -> Type {
        let nodes = || self.nodes.lock().unwrap_or_else(PoisonError::into_inner);
        if let Some(n) = nodes().get(&at).and_then(Weak::upgrade) {
            return Type(n);
        }
        // Made outside the lock; another thread that made one at the same time and kept it
        // first gives the one kept.
        let made = make();
        let kept = {
            let mut nodes = nodes();
            match nodes.get(&at).and_then(Weak::upgrade) {
                Some(n) => Type(n),
                None => {
                    nodes.insert(at, Arc::downgrade(&made.0));
                    made.clone()
                }
            }
        };
        drop(made);
        kept
    }

    /// Drops the recursive members it keeps, and the unfoldings of its members and parts still
    /// alive, which hold the members and one another: what is not held elsewhere is dropped. A
    /// member or part held elsewhere unfolds again when read, and stays the node of its place.
    // Complexity tradeoff (PERF-print-by-name-after-plain): forgetting the members' unfoldings
    // alone is O(members), but left a cycle of parts' unfoldings (`R0 = (#a, #a | R1)` keeps
    // `#a | R1` as a part whose unfolding holds the row of the next part), which kept the
    // instance and its group for the rest of the process once a print had unfolded the parts.
    // Used: every member and part is kept weakly by place ([`Env::nodes`]), and those alive are
    // forgotten here too, O(places alive or dead in the map) time per end of a unit that
    // registered the instance, at most the members and parts of the group's bodies, and a weak
    // handle each, which keeps a dropped node's allocation, not its contents, until this sweep.
    fn forget(&self) {
        let plain = &self.group().0.plain;
        let kept: Vec<Type> = (0..self.members.len())
            .filter(|&i| !plain[i])
            .filter_map(|i| self.cell(i).take())
            .collect();
        let alive: Vec<Type> = {
            let mut nodes = self.nodes.lock().unwrap_or_else(PoisonError::into_inner);
            nodes.retain(|_, n| n.strong_count() > 0);
            nodes.values().filter_map(Weak::upgrade).map(Type).collect()
        };
        for t in &alive {
            t.forget_unfolding();
        }
        drop((kept, alive));
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

    /// The name of the part kept unevaluated at `e`: the text of `e` at the arguments, made once
    /// per instance and kept in [`Env::part_names`] with the names of the parts inside it.
    // Complexity tradeoff (COMPLEXITY.md, row PERF-part-name-nested): a part's name spells out
    // its whole subexpression, so the parts nested inside it are spelled out again in each name
    // around them. Before, each part's name was made by its own walk of its subexpression: `k`
    // nested parts took O(k^2) time and memory (printing `print::tests::part_cycle` took 42.4
    // times the instructions and 46.4 times the bytes at 800 parts against 100). Used: the
    // names are shared as a DAG of ropes, the way hash-consing shares equal subterms (Goto,
    // "Monocopy and associative algorithms in extended Lisp", University of Tokyo, 1974) and a
    // rope holds its substrings by reference (Boehm, Atkinson and Plass, "Ropes: an alternative
    // to strings", Software: Practice and Experience, 1995). The walk for one part's name keeps
    // the name of each part met inside it, and takes the name of a part already kept as one
    // leaf, so the names of an instance's parts cost O(body) in all, each made once (building
    // and printing `part_cycle` now takes 9.98 times the instructions at 16,000 parts against
    // 2,000, within the printer's O(t log t) sort; `print::bench`). The text
    // is byte for byte the one spelled out, parentheses included, so the printer's ranking of
    // names (`Tok::Rec`) is unchanged, and `Key` and `canon` do not read names. Costs: one map
    // entry per part named, kept with the instance; a try that read a text not yet made keeps
    // nothing and is made again ([`Type::rope`]). Reading a name in full is still linear in
    // its text, which is quadratic in the nesting, as before.
    fn part_name(&self, e: &Node) -> Rope {
        let kept = || {
            self.part_names
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
        };
        if let Some(r) = kept().get(&e.at) {
            return r.clone();
        }
        let show = Show {
            defs: &self.group().0.defs,
            params: &[],
            args: Some(&self.args),
            e,
            surface: false,
        };
        let mut found = Vec::new();
        let r = show.rope_with(&mut |t, _| t.rope(), Some((&self.part_names, &mut found)));
        if types::showing_complete() {
            let mut kept = kept();
            for (at, inner) in found {
                kept.entry(at).or_insert(inner);
            }
            kept.entry(e.at).or_insert_with(|| r.clone());
        }
        r
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
                        // `Step::Eval` takes these three at once and pushes `Step::Build` only
                        // for the other shapes.
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
    let part = env.node(At::Part(e.at), || {
        let (named, at) = (e.clone(), env.clone());
        let key = Key::new(env.clone(), At::Part(e.at));
        let (e, made_in) = (e.clone(), env.clone());
        Type::rec(
            key,
            move || at.part_name(&named),
            move || eval(&e, &made_in),
        )
    });
    // Its unfolding, made in this unit, is forgotten at its end ([`Env::forget`]).
    env.register();
    part
}

/// Whether `e`, a part directly below an expression of shape `parent`, is kept unevaluated
/// ([`component`]) when the expression is evaluated.
fn kept_as_part(parent: &Shape, e: &Node) -> bool {
    matches!(
        parent,
        Shape::Tuple(_) | Shape::Atom(..) | Shape::Morphism(..)
    ) && !eager(e)
}

/// The names of an instance's parts kept so far, and those a walk made that were not kept
/// ([`Env::part_name`]).
type PartNames<'a> = (&'a Mutex<HashMap<u32, Rope>>, &'a mut Vec<(u32, Rope)>);

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
    /// The text spelled out in full, each part inside walked again rather than read from the
    /// names kept ([`Env::part_name`]).
    fn rope(&self) -> Rope {
        self.rope_with(&mut |t, _| t.rope(), None)
    }

    /// The text as a rope, which holds the texts of the types it names without copying them,
    /// so that the name of `Tree(Tree(..))` takes time linear in its text. Each expression's
    /// rope is built once its parts' are, from a stack. Each part is parenthesized only where
    /// the type grammar (DESIGN.md sec:grammar) would not read it as one operand of the part
    /// around it. Each type in the expression is given by `leaf` from the type and its place,
    /// called on the types in the order they are written. With `names`, the expression is a
    /// part of an instance at its arguments ([`Env::part_name`]): a part inside it kept
    /// unevaluated whose name is kept is written by that rope, and the name of each other one
    /// is added to the list.
    fn rope_with(
        &self,
        leaf: &mut dyn FnMut(&Type, Place) -> Rope,
        mut names: Option<PartNames<'_>>,
    ) -> Rope {
        /// A node, where it stands, and whether it is a part kept unevaluated.
        enum Step<'a> {
            Visit(&'a Node, Place, bool),
            Build(&'a Node, Place, bool),
        }
        let mut todo = vec![Step::Visit(self.e, Place::Any, false)];
        let mut done: Vec<Rope> = Vec::new();
        while let Some(step) = todo.pop() {
            let r = match step {
                Step::Visit(e, at, true)
                    if let Some((kept, _)) = &names
                        && let Some(r) = (kept.lock().unwrap_or_else(PoisonError::into_inner))
                            .get(&e.at)
                            .cloned() =>
                {
                    bracketed(r, &e.e, at)
                }
                Step::Visit(e, at, part) => match &e.e {
                    Shape::Param(i) => match self.args {
                        Some(args) => args[*i].rope(),
                        None => Rope::cat([Piece::from(self.params[*i].as_str())]),
                    },
                    Shape::Ref(i, args) if args.is_empty() => {
                        Rope::cat([Piece::from(self.defs[*i].name.as_str())])
                    }
                    Shape::Type(t) => leaf(t, at),
                    _ => {
                        todo.push(Step::Build(e, at, part));
                        let n = e.e.kids().count();
                        todo.extend(
                            (e.e.kids().rev().zip((0..n).rev()))
                                .filter(|&(_, i)| !unwritten(&e.e, i))
                                .map(|(c, i)| {
                                    Step::Visit(c, kid_place(&e.e, i), kept_as_part(&e.e, c))
                                }),
                        );
                        continue;
                    }
                },
                Step::Build(e, at, part) => {
                    let n = e.e.kids().count();
                    let written = (0..n).filter(|&i| !unwritten(&e.e, i)).count();
                    let parts = done.split_off(done.len() - written);
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
                            Shape::Morphism(..) if exact(&e.e) => {
                                Rope::joined("", parts, " -> ", "")
                            }
                            Shape::Morphism(l, _, _) if partial(l) => {
                                Rope::joined("", parts, " ->? ", "")
                            }
                            Shape::Morphism(..) => {
                                let v = parts.pop().expect("the value type");
                                let u_rope = parts.pop().expect("the permission");
                                let l_rope = parts.pop().expect("the guarantee");
                                Rope::cat([
                                    Piece::from(l_rope),
                                    Piece::from(" .. "),
                                    Piece::from(u_rope),
                                    Piece::from(" -> "),
                                    Piece::from(v),
                                ])
                            }
                            Shape::Param(_) | Shape::Ref(..) | Shape::Type(_) => {
                                // `Step::Visit` writes a `Param`, a `Type` and a `Ref` of no
                                // arguments at once, and a `Ref` built is taken by the `if
                                // let` above.
                                unreachable!("a leaf is not built")
                            }
                        }
                    };
                    if part && let Some((_, found)) = &mut names {
                        found.push((e.at, r.clone()));
                    }
                    bracketed(r, &e.e, at)
                }
            };
            done.push(r);
        }
        done.pop().expect("the rope of the expression")
    }
}

/// The rope `r` of an expression of shape `s` that is not a leaf, parenthesized where it stands
/// at `at` only if the type grammar would not read it there as one operand.
fn bracketed(r: Rope, s: &Shape, at: Place) -> Rope {
    match at.admits(class(s)) {
        true => r,
        false => Rope::joined("(", [r], "", ")"),
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

/// Whether `s` is an arrow whose guarantee is its permission, written `K -> V` with the key
/// once: its text holds no part for the permission.
fn exact(s: &Shape) -> bool {
    matches!(s, Shape::Morphism(l, u, _) if same(l, u))
}

/// Whether `l`, the guarantee of an arrow, is `Never`: the arrow is written `U ->? V`.
fn partial(l: &Node) -> bool {
    matches!(&l.e, Shape::Type(t) if *t == Type::empty())
}

/// Whether part `i` of an expression of shape `s` is left out of its text, and so is not
/// visited: the permission of an exact arrow, written once as its key, and the guarantee of a
/// partial one. A part printed and then dropped would drop with it the mark a message's naming
/// pass reads as the start of its printed types, when it is the first ([`Type::surfaces_by_name`]).
fn unwritten(s: &Shape, i: usize) -> bool {
    match s {
        Shape::Morphism(..) if exact(s) => i == 1,
        Shape::Morphism(l, _, _) => i == 0 && partial(l),
        _ => false,
    }
}

/// Where part `i` of the parts directly below an expression of shape `s` stands: `\` takes no
/// `&` or `|` on either side and no `\` on its right, an arrow's key and bounds no arrow and
/// no connective, since the bare `A | B -> V` is rejected (author P222), and its
/// key no tuple, which would read as its parameters (DESIGN.md sec:grammar). So a key is
/// parenthesized only where the grammar needs it (author rule P191): `K -> V`, `(A | B) -> V`,
/// and `((A, B)) -> V` for a tuple key.
fn kid_place(s: &Shape, i: usize) -> Place {
    let (each, fixed): (Place, [Option<Place>; 3]) = match s {
        Shape::Union(_) => (Place::Union, [None; 3]),
        Shape::And(_) => (Place::And, [None; 3]),
        Shape::Not(_) => (Place::Prim, [None; 3]),
        Shape::Diff(..) => (Place::Any, [Some(Place::DiffLeft), Some(Place::Prim), None]),
        Shape::Morphism(..) if exact(s) => (Place::Any, [Some(Place::Key), None, None]),
        Shape::Morphism(l, _, _) if partial(l) => (
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

mod show;

#[cfg(test)]
mod tests;
