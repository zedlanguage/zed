//! The operations on [`Value`] that follow its nesting: drop, compare, copy and show. Each keeps
//! its own stack on the heap, so a value's depth is limited by the machine's memory alone
//! (DESIGN.md sec:kernel, "Reference semantics"), and each costs O(size).

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::mem;
use std::slice;
use std::sync::Arc;
use std::thread::LocalKey;

use imbl::OrdMap;
use imbl::ordmap::Iter;
use imbl::shared_ptr::DefaultSharedPtr;

use crate::family::Family;
use crate::value::{Atom, Items, Value};

/// The addresses of two shared sequences under comparison. A walk keeps a pair only while it
/// borrows both values, so no address can be freed and reused while the pair is held.
pub(crate) type Pair = (usize, usize);

/// A part of a value whose owner is being dropped. A family's map is freed whole: the map's own
/// nodes nest only as deep as its height, and the values inside it land here in turn.
#[expect(dead_code, reason = "a part is held only to be dropped")]
pub(crate) enum Part {
    Items(Arc<[Value]>),
    Map(OrdMap<Value, Value>),
}

thread_local! {
    /// The parts of values waiting to be dropped.
    static PARTS: Queue<Part> = const { Queue::new() };
    /// Whether a comparison further up this thread's stack is already reading [`PAIRS`].
    static COMPARING: Cell<bool> = const { Cell::new(false) };
    /// The pairs of families a comparison has yet to read.
    static PAIRS: RefCell<Vec<(Family, Family)>> = const { RefCell::new(Vec::new()) };
}

/// A thread's parts of one kind waiting to be dropped, for [`free_in`].
pub(crate) struct Queue<T> {
    /// Whether a drop further up this thread's stack is already emptying `parts`.
    busy: Cell<bool>,
    parts: RefCell<Vec<T>>,
}

impl<T> Queue<T> {
    pub(crate) const fn new() -> Queue<T> {
        Queue {
            busy: Cell::new(false),
            parts: RefCell::new(Vec::new()),
        }
    }
}

/// Drops `part`. A drop reached from inside this one queues its part and returns, so a chain of
/// parts is freed in a loop, whichever containers lie between them.
pub(crate) fn free(part: Part) {
    free_in(&PARTS, part);
}

/// Drops `part` with the thread's `queue`, as [`free`] does. While the thread is ending and its
/// queue is gone, the part is dropped here, by recursion; [`hold`] keeps a queue until after the
/// tables that hold its parts are gone.
pub(crate) fn free_in<T: 'static>(queue: &'static LocalKey<Queue<T>>, part: T) {
    let mut held = Some(part);
    let first = queue.try_with(|q| {
        if q.busy.replace(true) {
            q.parts.borrow_mut().extend(held.take());
            false
        } else {
            true
        }
    });
    if !matches!(first, Ok(true)) {
        return;
    }
    drop(held);
    // The borrow ends with the pop: dropping a part can reach `free_in` again.
    while let Ok(Some(next)) = queue.try_with(|q| q.parts.borrow_mut().pop()) {
        drop(next);
    }
    let _ = queue.try_with(|q| q.busy.set(false));
}

/// Makes `queue` outlive every thread-local made after this call. A thread's locals are dropped
/// in the reverse of the order in which they were first used, so a table first used after this
/// call is dropped while the queue is still there to free its parts in a loop.
pub(crate) fn hold<T: 'static>(queue: &'static LocalKey<Queue<T>>) {
    let _ = queue.try_with(|_| ());
}

/// Which relation a walk over two values computes.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Relation {
    /// The total order of [`Ord`].
    Total,
    /// Equality of [`PartialEq`], the ties of the total order. It tests sizes first, and it
    /// reads two families with `diff`, which skips the nodes they share.
    Identity,
    /// The language's `==`: [`Relation::Identity`] with IEEE 754 floats.
    SurfaceEq,
    /// The language's order: IEEE 754 floats, and tuples by component.
    SurfaceOrder,
}

/// The two sequences of entries under comparison at one depth.
enum Level<'a> {
    /// The two sequences, and the pair of their addresses when either is shared, so a pair
    /// met again through the sharing is not read again.
    Items(
        slice::Iter<'a, Value>,
        slice::Iter<'a, Value>,
        Relation,
        Option<Pair>,
    ),
    /// On the heap: a map iterator is many times the size of a slice iterator, and tuples
    /// are the common level.
    Maps(Box<MapLevel<'a>>),
}

/// The entries of two families under comparison.
struct MapLevel<'a> {
    a: Iter<'a, Value, Value, DefaultSharedPtr>,
    b: Iter<'a, Value, Value, DefaultSharedPtr>,
    /// The values of the entry whose keys were compared last.
    values: Option<(&'a Value, &'a Value)>,
    relation: Relation,
}

/// What one comparison found.
enum Step<'a> {
    /// The two are the same so far.
    Same,
    /// The result of the whole walk: a difference, or `None` for an unordered pair.
    Ends(Option<Ordering>),
    /// The two are the same only if their parts are.
    Enter(Level<'a>),
    /// The level has no entries left on either side.
    Done,
}

fn items<'a>(a: &'a Items, b: &'a Items, r: Relation) -> Step<'a> {
    match r {
        // One shared sequence is bitwise equal to itself; the IEEE 754 relations read it,
        // since a NaN inside is not equal to itself.
        Relation::Identity | Relation::Total if a.ptr_eq(b) => Step::Same,
        Relation::Identity | Relation::SurfaceEq if a.len() != b.len() => Step::Ends(None),
        _ => Step::Enter(Level::Items(a.iter(), b.iter(), r, Items::pair(a, b))),
    }
}

fn atoms<'a>(a: &'a Atom, b: &'a Atom, r: Relation) -> Step<'a> {
    match a.name.cmp(&b.name).then_with(|| a.fields.cmp(&b.fields)) {
        Ordering::Equal => items(&a.args, &b.args, r),
        o => Step::Ends(Some(o)),
    }
}

fn maps<'a>(a: &'a Family, b: &'a Family, r: Relation) -> Step<'a> {
    let same = a.0.ptr_eq(&b.0);
    match r {
        Relation::Identity | Relation::SurfaceEq if a.len() != b.len() => Step::Ends(None),
        Relation::Identity if same => Step::Same,
        Relation::Identity => {
            // A family is copied by a reference count, so the queue holds no data.
            PAIRS.with_borrow_mut(|pairs| pairs.push((a.clone(), b.clone())));
            Step::Same
        }
        Relation::Total if same => Step::Same,
        _ => Step::Enter(Level::Maps(Box::new(MapLevel {
            a: a.0.iter(),
            b: b.0.iter(),
            values: None,
            relation: r,
        }))),
    }
}

/// Compares two values as far as their top level decides.
fn step<'a>(a: &'a Value, b: &'a Value, r: Relation) -> Step<'a> {
    match (a, b, r) {
        (Value::Float(x), Value::Float(y), Relation::SurfaceEq) => match x.get() == y.get() {
            true => Step::Same,
            false => Step::Ends(None),
        },
        (Value::Float(x), Value::Float(y), Relation::SurfaceOrder) => {
            match x.get().partial_cmp(&y.get()) {
                Some(Ordering::Equal) => Step::Same,
                o => Step::Ends(o),
            }
        }
        (Value::Tuple(x), Value::Tuple(y), _) => items(x, y, r),
        (_, _, Relation::SurfaceOrder) => match a.cmp(b) {
            Ordering::Equal => Step::Same,
            o => Step::Ends(Some(o)),
        },
        (Value::Path(x), Value::Path(y), _) => items(x, y, r),
        (Value::Atom(x), Value::Atom(y), _) => atoms(x, y, r),
        (Value::Family(x), Value::Family(y), _) => maps(x, y, r),
        _ => match a.scalar_cmp(b) {
            Ordering::Equal => Step::Same,
            o => Step::Ends(Some(o)),
        },
    }
}

/// The end of a level at which one side has `a` left and the other `b`.
fn side<'a>(a: bool, b: bool) -> Step<'a> {
    match (a, b) {
        (false, false) => Step::Done,
        (false, true) => Step::Ends(Some(Ordering::Less)),
        (true, _) => Step::Ends(Some(Ordering::Greater)),
    }
}

/// Takes the next entry of `level`.
fn advance<'a>(level: &mut Level<'a>) -> Step<'a> {
    match level {
        Level::Items(a, b, r, _) => match (a.next(), b.next()) {
            (Some(x), Some(y)) => step(x, y, *r),
            (x, y) => side(x.is_some(), y.is_some()),
        },
        Level::Maps(level) => {
            if let Some((v, w)) = level.values.take() {
                return step(v, w, level.relation);
            }
            match (level.a.next(), level.b.next()) {
                (Some((k, v)), Some((l, w))) => {
                    level.values = Some((v, w));
                    // Keys are compared bitwise whichever relation the values are compared by.
                    step(k, l, Relation::Total)
                }
                (x, y) => side(x.is_some(), y.is_some()),
            }
        }
    }
}

/// Runs a walk from its first step to the first difference. `None` is an unordered pair; a walk
/// that ends without one gives `Some(Equal)`. A flat value needs no heap: the stack holds only
/// the levels above the one in hand. Shared tuples make a value a DAG, so a pair of shared
/// sequences read to its end is kept, and met again it is the same without a second reading:
/// the walk is O(distinct pairs), not O(paths).
fn walk(first: Step<'_>) -> Option<Ordering> {
    let mut level = match first {
        Step::Same | Step::Done => return Some(Ordering::Equal),
        Step::Ends(o) => return o,
        Step::Enter(level) => level,
    };
    let mut above = Vec::new();
    let mut read = HashSet::new();
    loop {
        match advance(&mut level) {
            Step::Same => {}
            Step::Ends(o) => return o,
            Step::Enter(Level::Items(.., r, Some(pair))) if read.contains(&(pair, r)) => {}
            Step::Enter(inner) => above.push(mem::replace(&mut level, inner)),
            Step::Done => {
                if let Level::Items(.., r, Some(pair)) = level {
                    read.insert((pair, r));
                }
                match above.pop() {
                    Some(outer) => level = outer,
                    None => return Some(Ordering::Equal),
                }
            }
        }
    }
}

/// Finishes an identity walk that found `same` so far by reading the queued families. A walk
/// started while the queue is being read leaves its families in the queue: `diff` calls `==`
/// on the entries it finds, inside imbl, where no stack of ours can reach, and this keeps that
/// call from nesting.
fn settle(same: bool) -> bool {
    if COMPARING.get() {
        return same;
    }
    COMPARING.set(true);
    let mut all = same;
    while all && let Some((a, b)) = PAIRS.with_borrow_mut(Vec::pop) {
        all = a.0.diff(&b.0).next().is_none();
    }
    COMPARING.set(false);
    let left = PAIRS.with_borrow_mut(mem::take);
    drop(left);
    all
}

/// Whether two sequences of values are the same.
pub(crate) fn items_eq(a: &Items, b: &Items) -> bool {
    settle(walk(items(a, b, Relation::Identity)) == Some(Ordering::Equal))
}

/// Whether two families are the same.
pub(crate) fn families_eq(a: &Family, b: &Family) -> bool {
    settle(walk(maps(a, b, Relation::Identity)) == Some(Ordering::Equal))
}

/// The total order on two sequences of values.
pub(crate) fn items_cmp(a: &Items, b: &Items) -> Ordering {
    walk(items(a, b, Relation::Total)).expect("the total order orders every pair")
}

/// The total order on two families.
pub(crate) fn families_cmp(a: &Family, b: &Family) -> Ordering {
    walk(maps(a, b, Relation::Total)).expect("the total order orders every pair")
}

/// The total order on two values.
pub(crate) fn cmp(a: &Value, b: &Value) -> Ordering {
    walk(step(a, b, Relation::Total)).expect("the total order orders every pair")
}

/// The language's `==`.
pub(crate) fn surface_eq(a: &Value, b: &Value) -> bool {
    walk(step(a, b, Relation::SurfaceEq)) == Some(Ordering::Equal)
}

/// The language's order; `None` when the two are unordered.
pub(crate) fn surface_cmp(a: &Value, b: &Value) -> Option<Ordering> {
    walk(step(a, b, Relation::SurfaceOrder))
}

/// What a sequence of copied values is rebuilt into.
enum Shape<'a> {
    Tuple,
    Path,
    Atom(&'a Atom),
}

impl Shape<'_> {
    fn wrap(&self, items: Items) -> Value {
        match self {
            Shape::Tuple => Value::Tuple(items),
            Shape::Path => Value::Path(items),
            Shape::Atom(a) => Value::Atom(Atom {
                name: a.name.clone(),
                fields: a.fields.clone(),
                args: items,
            }),
        }
    }
}

/// A sequence of values being copied.
struct Copying<'a> {
    left: slice::Iter<'a, Value>,
    done: Vec<Value>,
    shape: Shape<'a>,
    /// The address of the sequence copied, when it is shared and so can be met again.
    shared: Option<usize>,
}

impl<'a> Copying<'a> {
    fn new(from: &'a [Value], shape: Shape<'a>, shared: Option<usize>) -> Self {
        Copying {
            left: from.iter(),
            done: Vec::with_capacity(from.len()),
            shape,
            shared,
        }
    }
}

/// Copies `from`, tuples, keypaths and atoms' payloads to any depth, and every other value
/// through `leaf`. A shared sequence is copied once, and its copy is shared in the same places,
/// so the copy of a DAG is a DAG of the same size.
pub(crate) fn copy(from: &[Value], leaf: fn(&Value) -> Value) -> Vec<Value> {
    let mut level = Copying::new(from, Shape::Tuple, None);
    let mut above = Vec::new();
    let mut copied: HashMap<usize, Items> = HashMap::new();
    loop {
        let (xs, shape) = match level.left.next() {
            Some(Value::Tuple(xs)) => (xs, Shape::Tuple),
            Some(Value::Path(xs)) => (xs, Shape::Path),
            Some(Value::Atom(a)) => (&a.args, Shape::Atom(a)),
            Some(v) => {
                level.done.push(leaf(v));
                continue;
            }
            None => match above.pop() {
                Some(outer) => {
                    let inner = mem::replace(&mut level, outer);
                    let items = Items::from(inner.done);
                    if let Some(at) = inner.shared {
                        copied.insert(at, items.clone());
                    }
                    level.done.push(inner.shape.wrap(items));
                    continue;
                }
                None => return level.done,
            },
        };
        let shared = xs.is_shared().then(|| xs.addr());
        match shared.and_then(|at| copied.get(&at)) {
            Some(items) => level.done.push(shape.wrap(items.clone())),
            None => above.push(mem::replace(&mut level, Copying::new(xs, shape, shared))),
        }
    }
}

/// Whether `test` holds of every value in `from`, tuples, keypaths and atoms' payloads read to
/// any depth, stopping at the first that fails. A shared sequence is read once.
pub(crate) fn all_leaves(from: &[Value], test: fn(&Value) -> bool) -> bool {
    let mut level = from.iter();
    let mut above = Vec::new();
    let mut read = HashSet::new();
    loop {
        let inner = match level.next() {
            Some(Value::Tuple(xs) | Value::Path(xs)) => xs,
            Some(Value::Atom(a)) => &a.args,
            Some(v) if test(v) => continue,
            Some(_) => return false,
            None => match above.pop() {
                Some(outer) => {
                    level = outer;
                    continue;
                }
                None => return true,
            },
        };
        if inner.is_shared() && !read.insert(inner.addr()) {
            continue;
        }
        above.push(mem::replace(&mut level, inner.iter()));
    }
}

/// What is left to write.
enum Task<'a> {
    Text(&'a str),
    Quoted(&'a str),
    Show(&'a Value),
    Debug(&'a Value),
    Family(&'a Family),
    DebugFamily(&'a Family),
}

/// `list` as tasks in reverse, each entry after the first preceded by `sep`, for a stack.
fn push_list<'a>(
    todo: &mut Vec<Task<'a>>,
    list: &'a [Value],
    sep: &'static str,
    task: fn(&'a Value) -> Task<'a>,
) {
    for (i, v) in list.iter().enumerate().rev() {
        todo.push(task(v));
        if i > 0 {
            todo.push(Task::Text(sep));
        }
    }
}

fn show_atom<'a>(a: &'a Atom, todo: &mut Vec<Task<'a>>) {
    if a.args.is_empty() {
        return;
    }
    todo.push(Task::Text(")"));
    for (i, v) in a.args.iter().enumerate().rev() {
        todo.push(Task::Show(v));
        if let Some(k) = a.fields.get(i) {
            todo.extend([Task::Text(": "), Task::Text(k)]);
        }
        if i > 0 {
            todo.push(Task::Text(", "));
        }
    }
    todo.push(Task::Text("("));
}

fn show_family<'a>(fam: &'a Family, todo: &mut Vec<Task<'a>>) {
    // A set, each leaf its own key (`k -> k`), is written by its members.
    let set = !fam.is_empty() && fam.0.iter().all(|(k, v)| k == v);
    todo.push(Task::Text("}"));
    let last = fam.len();
    for (i, (k, v)) in fam.0.iter().rev().enumerate() {
        if !set {
            todo.extend([Task::Show(v), Task::Text(" -> ")]);
        }
        todo.push(Task::Show(k));
        if i + 1 < last {
            todo.push(Task::Text(", "));
        }
    }
    todo.push(Task::Text("{"));
}

/// The form of `{}`: one step of showing `v`.
fn show<'a>(v: &'a Value, f: &mut fmt::Formatter<'_>, todo: &mut Vec<Task<'a>>) -> fmt::Result {
    match v {
        Value::Bool(b) => write!(f, "{b}"),
        Value::Int(n) => write!(f, "{n}"),
        Value::Big(n) => write!(f, "{}", n.numer_text()),
        Value::Rat(r) => write!(f, "{r}"),
        Value::Float(x) => write!(f, "{}", crate::num::show_f64(x.get())),
        Value::Str(s) => write!(f, "{s:?}"),
        Value::Atom(a) => {
            show_atom(a, todo);
            todo.push(Task::Text(&a.name));
            f.write_str("#")
        }
        Value::Tuple(items) => {
            todo.push(Task::Text(")"));
            push_list(todo, items, ", ", Task::Show);
            f.write_str("(")
        }
        Value::Path(keys) => {
            todo.push(Task::Text("]"));
            push_list(todo, keys, " -> ", Task::Show);
            f.write_str("[")
        }
        Value::Family(fam) => {
            todo.push(Task::Family(fam));
            Ok(())
        }
    }
}

fn debug_list<'a>(todo: &mut Vec<Task<'a>>, list: &'a [Value], close: &'static str) {
    todo.push(Task::Text(close));
    push_list(todo, list, ", ", Task::Debug);
}

fn debug_family<'a>(fam: &'a Family, todo: &mut Vec<Task<'a>>) {
    todo.push(Task::Text("})"));
    let last = fam.len();
    for (i, (k, v)) in fam.0.iter().rev().enumerate() {
        todo.extend([Task::Debug(v), Task::Text(": "), Task::Debug(k)]);
        if i + 1 < last {
            todo.push(Task::Text(", "));
        }
    }
    todo.push(Task::Text("Family({"));
}

/// The form of `{:?}`, as a derived `Debug` prints it: one step of showing `v`.
fn debug<'a>(v: &'a Value, f: &mut fmt::Formatter<'_>, todo: &mut Vec<Task<'a>>) -> fmt::Result {
    match v {
        Value::Bool(b) => write!(f, "Bool({b:?})"),
        Value::Int(n) => write!(f, "Int({n:?})"),
        Value::Big(n) => write!(f, "Big({n:?})"),
        Value::Rat(r) => write!(f, "Rat({r:?})"),
        Value::Float(x) => write!(f, "Float({x:?})"),
        Value::Str(s) => write!(f, "Str({s:?})"),
        Value::Atom(a) => {
            todo.push(Task::Text(" })"));
            debug_atom(a, todo);
            f.write_str("Atom(")
        }
        Value::Tuple(items) => {
            debug_list(todo, items, "])");
            f.write_str("Tuple([")
        }
        Value::Path(keys) => {
            debug_list(todo, keys, "])");
            f.write_str("Path([")
        }
        Value::Family(fam) => {
            todo.extend([Task::Text(")"), Task::DebugFamily(fam)]);
            f.write_str("Family(")
        }
    }
}

/// An atom's fields as tasks, without the closing `}`, which [`debug`] pushes.
fn debug_atom<'a>(a: &'a Atom, todo: &mut Vec<Task<'a>>) {
    debug_list(todo, &a.args, "]");
    todo.push(Task::Text("], args: ["));
    for (i, name) in a.fields.iter().enumerate().rev() {
        todo.push(Task::Quoted(name));
        if i > 0 {
            todo.push(Task::Text(", "));
        }
    }
    todo.extend([
        Task::Text(", fields: ["),
        Task::Quoted(&a.name),
        Task::Text("Atom { name: "),
    ]);
}

fn run<'a>(mut todo: Vec<Task<'a>>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    while let Some(task) = todo.pop() {
        match task {
            Task::Text(s) => f.write_str(s)?,
            Task::Quoted(s) => write!(f, "{s:?}")?,
            Task::Show(v) => show(v, f, &mut todo)?,
            Task::Debug(v) => debug(v, f, &mut todo)?,
            Task::Family(fam) => show_family(fam, &mut todo),
            Task::DebugFamily(fam) => debug_family(fam, &mut todo),
        }
    }
    Ok(())
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(vec![Task::Show(self)], f)
    }
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(vec![Task::Debug(self)], f)
    }
}

impl fmt::Display for Family {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(vec![Task::Family(self)], f)
    }
}

impl fmt::Debug for Family {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        run(vec![Task::DebugFamily(self)], f)
    }
}

impl fmt::Debug for Items {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("[")?;
        let mut todo = Vec::new();
        debug_list(&mut todo, self, "]");
        run(todo, f)
    }
}
