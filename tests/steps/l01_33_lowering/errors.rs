//! What the lowering refuses, and why.

use zed_kernel::term::build::{lam, let_, lit, prim, var};
use zed_kernel::{Prim, Term, Value};
use zed_tests::kernel::fold;
use zedc::zir::lower::{lower, raise};
use zedc::zir::{Region, RegionKind, Src};

fn push(port: &str, v: Term) -> Term {
    Term::Push(port.into(), v.into())
}

#[test]
fn a_port_inside_a_fold_is_refused() {
    let xs = lit(zed_kernel::Family::set([1, 2].map(Value::Int)));
    let leak = fold(xs, lam(&["a", "b"], push("stdout", var("a"))), None);
    assert_eq!(
        lower(&leak).unwrap_err(),
        "port `stdout` is used inside a function region, and a state edge enters only a match \
         or port region (step L1.31): a port is read or pushed outside functions, loops and \
         families, or in a function inlined there"
    );
}

#[test]
fn a_function_that_pushes_is_only_called() {
    let say = || lam(&["m"], push("stdout", var("m")));
    let as_value = let_("say", say(), prim(Prim::Tuple, vec![var("say")]));
    assert_eq!(
        lower(&as_value).unwrap_err(),
        "a function of 1 parameter that uses a port is used as a value: a function region \
         carries no state edge, so such a function is only called, and each call is inlined"
    );
    let two = let_(
        "say",
        say(),
        Term::App(var("say").into(), vec![lit("a"), lit("b")]),
    );
    assert_eq!(
        lower(&two).unwrap_err(),
        "a function of 1 parameter that uses a port is called with 2 arguments"
    );
}

#[test]
fn names_and_primitives_are_checked() {
    assert_eq!(
        lower(&var("ghost")).unwrap_err(),
        "`ghost` is not bound, and a term lowers only when every name it reads is bound in it \
         or is a prelude word"
    );
    let tuple = let_("t", Term::PrimFn(Prim::Tuple), var("t"));
    assert!(
        lower(&tuple)
            .unwrap_err()
            .ends_with("takes any number of arguments, so with no inputs its node is a call, not the function; call it instead of passing it as a value")
    );
    let neg = prim(Prim::Neg, vec![lit(1), lit(2)]);
    assert!(
        lower(&neg)
            .unwrap_err()
            .ends_with("takes 1 argument and is given 2")
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
