//! Deep values and the stack they are tested on, for the tests of step M0.9.

use zed_kernel::term::build::{app, if_, lam, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::{Family, Prim, Term, Value};

use crate::kernel::*;

/// Runs `f` on a thread with the 8 MiB stack of a main thread.
pub fn on_main_sized_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        let thread = std::thread::Builder::new().stack_size(1 << 23);
        thread.spawn_scoped(scope, f).unwrap().join().unwrap()
    })
}

/// `list(k) = if k == 0 { 0 } else { (k, list(k - 1)) }`: the list `(k, (k - 1, ... (1, 0)))`,
/// one call deep per element.
pub fn linked_list(k: i64) -> Term {
    let me = app(var("me"), vec![var("me"), sub(var("k"), lit(1))]);
    let body = if_(
        eq(var("k"), lit(0)),
        lit(0),
        prim(Prim::Tuple, vec![var("k"), me]),
    );
    let f = lam(&["me", "k"], body);
    app(f.clone(), vec![f, lit(k)])
}

/// One way to put a value inside another: a program's list, keypath, tree or nested record.
pub type Wrap = fn(Value, usize) -> Value;

/// `(k, v)`.
pub fn in_tuple(v: Value, k: usize) -> Value {
    Value::tuple(vec![Value::Int(k as i64), v])
}

/// The keypath `k -> v`.
pub fn in_path(v: Value, k: usize) -> Value {
    Value::path(vec![Value::Int(k as i64), v])
}

/// `#cons(k, v)`.
pub fn in_atom(v: Value, k: usize) -> Value {
    Value::atom_with("cons", vec![Value::Int(k as i64), v])
}

/// `#node(next: v)`.
pub fn in_named_atom(v: Value, _k: usize) -> Value {
    Value::atom_named("node", vec![("next".into(), v)]).expect("one field")
}

/// The family `{0 -> v}`.
pub fn in_family(v: Value, _k: usize) -> Value {
    Value::Family(Family::of([(0, v)]))
}

/// Each of the other kinds of wrapper, by `k`.
pub fn in_each_in_turn(v: Value, k: usize) -> Value {
    match k % 4 {
        0 => in_tuple(v, k),
        1 => in_atom(v, k),
        2 => in_path(v, k),
        _ => in_family(v, k),
    }
}

/// Every wrapper, by name.
pub const SHAPES: [(&str, Wrap); 6] = [
    ("tuples", in_tuple),
    ("paths", in_path),
    ("atoms", in_atom),
    ("named atoms", in_named_atom),
    ("families", in_family),
    ("all of them in turn", in_each_in_turn),
];

/// `bottom` inside `depth` wrappers.
pub fn nested(wrap: Wrap, depth: usize, bottom: Value) -> Value {
    (0..depth).fold(bottom, wrap)
}

/// `bottom` inside `depth` tuples.
pub fn int_list(depth: usize, bottom: Value) -> Value {
    nested(in_tuple, depth, bottom)
}

/// `type L = #nil | #cons(int, L)`.
pub fn list_type() -> Type {
    let cons = Expr::Atom(
        "cons".into(),
        vec![Expr::Type(Type::int()), Expr::Ref(0, vec![])],
    );
    let body = Expr::Union(vec![Expr::Type(Type::atom("nil")), cons]);
    let def = Def {
        name: "L".into(),
        params: vec![],
        body,
    };
    Group::new(vec![def]).unwrap().instance(vec![]).remove(0)
}
