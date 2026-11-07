//! `print::written`: a term on one line with each binder by the name the program wrote and the
//! elaborated `&&` and `||` written back, for a message (NAME-at-print-warnings).

use zed_kernel::Prim;
use zed_kernel::Term;
use zed_kernel::print::{pretty, written};
use zed_kernel::term::build::{app, if_, lam, let_, lit, prim, var};

/// The part of a kernel name before `@`, as `zedc::elab::written_name` gives it.
fn before_at(k: &str) -> &str {
    k.split_once('@').map_or(k, |(w, _)| w)
}

fn ge0(x: &str) -> Term {
    prim(Prim::Ge, vec![var(x), lit(0)])
}

/// Each place a binder is named is written through the function: a name read, a lambda's
/// parameters, a let's binder, the head of a call. A temporary `$k` has no `@` and stays.
#[test]
fn every_binder_is_named_through_the_function() {
    let t = let_(
        "g@1",
        lam(
            &["x@1", "y@1"],
            prim(Prim::Add, vec![var("x@1"), var("y@1")]),
        ),
        app(var("g@1"), vec![var("x@2"), var("$3")]),
    );
    assert_eq!(
        written(&t, before_at),
        "{ g = (x, y) -> (x + y); g(x, $3) }"
    );
    // Display is unchanged.
    assert_eq!(
        t.to_string(),
        "{ g@1 = (x@1, y@1) -> (x@1 + y@1); g@1(x@2, $3) }"
    );
}

/// `a && b` elaborates to `if a { b } else { false }` and `a || b` to `if a { true } else { b }`
/// (elab/walk.rs): written, each is the operator again, in parentheses as every binary
/// operator is. Any other `if` is written as it is, and `pretty` keeps the `if` form.
#[test]
fn the_elaborated_and_and_or_are_written_as_operators() {
    let and = if_(ge0("x@1"), ge0("y@2"), lit(false));
    assert_eq!(written(&and, before_at), "((x >= 0) && (y >= 0))");
    let or = if_(ge0("x"), lit(true), ge0("y"));
    assert_eq!(written(&or, before_at), "((x >= 0) || (y >= 0))");
    let nested = if_(if_(ge0("a"), ge0("b"), lit(false)), lit(true), ge0("c"));
    assert_eq!(
        written(&nested, before_at),
        "(((a >= 0) && (b >= 0)) || (c >= 0))"
    );
    let other = if_(ge0("x"), lit(1), lit(0));
    assert_eq!(written(&other, before_at), "if (x >= 0) { 1 } else { 0 }");
    assert_eq!(
        pretty(&and, usize::MAX),
        "if (x@1 >= 0) { (y@2 >= 0) } else { false }"
    );
}

/// The text is linear in the term: `k` tests joined by `&&`, nested to the left and to the
/// right, each name renamed.
#[test]
fn written_text_scales_with_the_term() {
    let chain = |k: usize, left: bool| -> Term {
        (1..k).fold(ge0("v@0"), |t, i| {
            let next = ge0(&format!("v@{i}"));
            if left {
                if_(t, next, lit(false))
            } else {
                if_(next, t, lit(false))
            }
        })
    };
    zed_tests::deep::on_small_stack(|| {
        for left in [true, false] {
            let n = 2_000;
            let inputs = [n, zed_tests::scaling::FACTOR * n].map(|k| chain(k, left));
            let what = if left { "left" } else { "right" };
            zed_tests::scaling::check(&format!("written, && nested to the {what}"), n, |k| {
                let t = &inputs[usize::from(k != n)];
                std::hint::black_box(written(t, before_at));
            });
        }
    });
}
