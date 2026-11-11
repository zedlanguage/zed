//! Deep values and the stack they are tested on, for the tests of step M0.9.

use zed_kernel::term::build::{app, if_, lam, lit, prim, var};
use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::{Family, Prim, Term, Value};

use crate::kernel::*;

/// Runs `f` on a thread with the 8 MiB stack of a main thread, the bytes it allocates counted
/// as this thread's ([`crate::scaling::on_a_thread`]).
pub fn on_main_sized_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    crate::scaling::on_a_thread(1 << 23, f)
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

/// Runs `f` on a thread with a 2 MiB stack, the default of a test thread, whatever
/// `RUST_MIN_STACK` says.
pub fn on_small_stack<T: Send>(f: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        let thread = std::thread::Builder::new().stack_size(2 << 20);
        thread.spawn_scoped(scope, f).unwrap().join().unwrap()
    })
}

/// A program whose text nests `n` deep, as a generator writes one, and what it prints.
pub struct Program {
    /// What nests.
    pub shape: &'static str,
    /// The source text.
    pub text: String,
    /// What `main` pushes to `stdout`.
    pub prints: String,
}

/// `main` printing `prefix` + `body` + `suffix`, inside a string hole.
fn printing(top: &str, hole: String, prints: String, shape: &'static str) -> Program {
    let text = format!("{top}main(m: MainArgs) {{\n  m.stdout <- \"${{{hole}}}\";\n}}\n");
    Program {
        shape,
        text,
        prints,
    }
}

/// Every shape of deep program, `n` deep, `n` at least 4: a left-nested sum, a right-nested
/// sum in parentheses, nested blocks, an `else if` chain, nested negations, nested calls, a
/// long sum in a function's body, nested tuples and nested lambdas.
pub fn programs(n: usize) -> Vec<Program> {
    assert!(n >= 4, "a deep program is at least 4 deep");
    let ones = vec!["1"; n].join(" + ");
    let paren = "(1 + ".repeat(n - 1) + "1" + &")".repeat(n - 1);
    let blocks = "{ return ".repeat(n) + "c" + &"; }".repeat(n);
    let ifs: String = (0..n)
        .map(|i| format!("if x == {i} {{ {i} }} else "))
        .collect::<String>()
        + "{ 0 }";
    let neg = "-".repeat(n) + "1";
    let calls = "f(".repeat(n) + "1" + &")".repeat(n);
    let tuple = "(".repeat(n) + "1" + &", 0)".repeat(n);
    let lams: String = (0..n).map(|i| format!("(x{i}) -> ")).collect::<String>() + "1";
    let done = |shape, body: String| Program {
        shape,
        text: format!("main(m: MainArgs) {{\n  t = {body};\n  m.stdout <- \"done\";\n}}\n"),
        prints: "done".into(),
    };
    vec![
        printing("", ones, n.to_string(), "a left-nested sum"),
        printing("", paren, n.to_string(), "a sum nested in parentheses"),
        printing(
            &format!("c = 1;\nv = {blocks};\n"),
            "v".into(),
            "1".into(),
            "nested blocks",
        ),
        printing("x = 3;\n", ifs, "3".into(), "an `else if` chain"),
        printing(
            "",
            neg,
            if n.is_multiple_of(2) { "1" } else { "-1" }.into(),
            "nested negations",
        ),
        printing(
            "f(positional x) = x + 1;\n",
            calls,
            (n + 1).to_string(),
            "nested calls",
        ),
        printing(
            &format!("f(positional x) = x + {};\n", vec!["1"; n - 1].join(" + ")),
            "f(1)".into(),
            n.to_string(),
            "a long sum in a function's body",
        ),
        done("nested tuples", tuple),
        done("nested lambdas", lams),
    ]
}

/// The program of shape `shape`, one of those [`programs`] gives, `n` deep.
pub fn program(shape: &str, n: usize) -> Program {
    let mut all = programs(n);
    let i = all.iter().position(|p| p.shape == shape);
    all.swap_remove(i.unwrap_or_else(|| panic!("no deep program of shape {shape}")))
}

/// The statements of `text`, lexed, parsed and built, for a test to build before it times a
/// later pass.
pub fn statements(text: &str) -> Vec<zedc::ast::Stmt> {
    let tokens = zedc::lex::lex_fence(text).unwrap();
    let tree = zedc::parse::parse(text, &tokens, "Unit", zedc::parse::TOP).unwrap();
    zedc::ast::unit(text, &tokens, &tree).unwrap()
}

/// The [`statements`] of `text` and their resolution, for a test to build before it times the
/// checker alone (COMPLEXITY.md F85).
pub fn resolved(text: &str) -> (Vec<zedc::ast::Stmt>, zedc::resolve::Resolution) {
    let stmts = statements(text);
    let res = zedc::resolve::resolve(&stmts).unwrap_or_else(|e| panic!("{text}: {e:?}"));
    (stmts, res)
}
