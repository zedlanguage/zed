//! What the lowering refuses, and why.

use zed_kernel::term::build::{lam, let_, lit, prim, var};
use zed_kernel::{Prim, Term, Value};
use zed_tests::kernel::fold;
use zedc::zir::lower::{lower, raise};
use zedc::zir::{Region, RegionKind, Src};

/// The message for a term no checked program lowers to: a bug in zedc, with `detail`.
fn bug(detail: &str) -> String {
    format!(
        "zedc could not compile the program because of a bug in zedc, not in the program. \
         Please report it to the Zed developers with the program's source and this line: \
         {detail}. Until it is fixed, `zedc run` runs the program without compiling it"
    )
}

fn push(port: &str, v: Term) -> Term {
    Term::Push(port.into(), v.into())
}

#[test]
fn a_port_inside_a_fold_is_refused() {
    let xs = lit(zed_kernel::Family::set([1, 2].map(Value::Int)));
    let leak = fold(xs, lam(&["a", "b"], push("stdout", var("a"))), None);
    assert_eq!(
        lower(&leak).unwrap_err(),
        "`zedc build` cannot compile this program: it reads or pushes the port `stdout` inside \
         a function that is not bound by `let` and called by its name. Built code carries the \
         state of a port only into the arms of a `match` and into a function bound by `let` \
         and called by its name. Repairs: move the reads and pushes of `stdout` out of the \
         function and pass the values in or out; bind the function with `let` and call it by \
         its name; or run the program with `zedc run`, which has no such limit"
    );
}

#[test]
fn a_function_that_pushes_is_only_called() {
    let say = || lam(&["m"], push("stdout", var("m")));
    let as_value = let_("say", say(), prim(Prim::Tuple, vec![var("say")]));
    assert_eq!(
        lower(&as_value).unwrap_err(),
        "`zedc build` cannot compile this program: the function `say`, of 1 parameter, reads or \
         pushes the port `stdout`, and the program uses `say` as a value (it passes, stores or \
         returns it) instead of calling it. Built code carries the state of a port only through \
         a call that names the function, so `say` can only be called by its name. Repairs: \
         call `say` by its name where it is used; move the reads and pushes out of `say` and \
         pass the values in or out; or run the program with `zedc run`, which has no such limit"
    );
    let two = let_(
        "say",
        say(),
        Term::App(var("say").into(), vec![lit("a"), lit("b")]),
    );
    assert_eq!(
        lower(&two).unwrap_err(),
        bug(
            "the function `say`, of 1 parameter, that reads or pushes a port is called with 2 arguments"
        )
    );
}

#[test]
fn a_name_bound_inside_a_function_is_not_the_function_of_that_name_outside() {
    // `h` calls its own `say`, which pushes nothing, so `h` uses no port and is a value; with
    // the outer `say` called instead, `h` uses `stdout` and is only called.
    let h = |inner: bool| {
        let call = Term::App(var("say").into(), vec![var("v")]);
        let body = if inner {
            let_("say", lam(&["u"], var("u")), call)
        } else {
            call
        };
        let_(
            "say",
            lam(&["m"], push("stdout", var("m"))),
            let_("h", lam(&["v"], body), prim(Prim::Tuple, vec![var("h")])),
        )
    };
    lower(&h(true)).unwrap();
    assert!(
        lower(&h(false)).unwrap_err().starts_with(
            "`zedc build` cannot compile this program: the function `h`, of 1 parameter, reads or pushes the port `stdout`"
        )
    );
}

#[test]
fn names_and_primitives_are_checked() {
    assert_eq!(
        lower(&var("ghost")).unwrap_err(),
        bug(
            "`ghost` is not bound, and a term lowers only when every name it reads is bound in it or is a prelude word"
        )
    );
    let tuple = let_("t", Term::PrimFn(Prim::Tuple), var("t"));
    assert!(
        lower(&tuple)
            .unwrap_err()
            .ends_with("takes any number of arguments, so with no inputs its node is a call, not the function. Until it is fixed, `zedc run` runs the program without compiling it")
    );
    let neg = prim(Prim::Neg, vec![lit(1), lit(2)]);
    assert!(
        lower(&neg)
            .unwrap_err()
            .ends_with("takes 1 argument and is given 2. Until it is fixed, `zedc run` runs the program without compiling it")
    );
}

#[test]
fn raise_wants_one_value_and_a_state_per_port() {
    let g = Region {
        kind: RegionKind::Function,
        args: Vec::new(),
        nodes: Vec::new(),
        results: vec![Src::Const(Value::Int(1)), Src::Const(Value::Int(2))],
    };
    assert_eq!(
        raise(&g).unwrap_err(),
        "the root region has 0 arguments and 2 results, and a term's root has one value and \
         a state result for each state argument"
    );
}
