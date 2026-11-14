//! FAIL-zir-lower-port-in-family-message (TEST-complete-zir, author P189). Drop into
//! tests/steps/l01_33_lowering/ as a module (`mod fail_port_in_family;` in mod.rs) once the
//! refusal in crates/zedc-zir/src/zir/lower.rs `state()` names a family as a family.
//!
//! DESIGN L1.31: state edges enter only match and port regions and the function region of a
//! `lambda`; L1.33: a read or push elsewhere is refused. The refusal has a wording for "a loop
//! or a family", but a `fam` node's body region has kind `function`, so a push in a family's
//! body is described as "inside a function that is not bound by `let` and called by its name"
//! and the repair tells the user to bind it with `let`, which a family body cannot be. Error
//! messages use the program's words (standing rule on plain error messages), and the program
//! wrote a family.

use zed_kernel::term::build::{lam, lit, var};
use zed_kernel::{Family, Term, Value};
use zed_tests::kernel::{fam, fold};
use zedc::zir::lower::lower;

#[test]
fn a_port_in_a_family_s_body_is_refused_as_inside_a_family() {
    let set = || lit(Family::set([1, 2].map(Value::Int)));
    let cases = [
        (
            fam(set(), "i", Term::Push("stdout".into(), var("i").into())),
            "stdout",
        ),
        (fam(set(), "i", Term::Read("stdin".into())), "stdin"),
    ];
    let wrong: Vec<String> = cases
        .iter()
        .filter_map(|(t, port)| {
            let want = format!(
                "`zedc build` cannot compile this program: it reads or pushes the port `{port}` \
                 inside a loop or a family. Built code carries the state of a port only into \
                 the arms of a `match` and into a function bound by `let` and called by its \
                 name. Repairs: move the reads and pushes of `{port}` out of the loop or family \
                 and pass the values in or out; bind the function with `let` and call it by its \
                 name; or run the program with `zedc run`, which has no such limit"
            );
            let got = lower(t).err().unwrap_or_default();
            (got != want).then(|| format!("`{port}`: got {got:?}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// The refusal's opening for port `port` inside `inside`.
fn refused_inside(port: &str, inside: &str) -> String {
    format!(
        "`zedc build` cannot compile this program: it reads or pushes the port `{port}` {inside}."
    )
}

/// The neighbors: a family reached through the arms of an `if` in its body still names the
/// family; a lambda written inside a family's body, and a family's body inside a lambda's body,
/// each name the region nearest the port; a fold's operator stays a function.
#[test]
fn the_nearest_region_names_the_refusal() {
    let set = || lit(Family::set([1, 2].map(Value::Int)));
    let push = |v: Term| Term::Push("stdout".into(), v.into());
    let family = "inside a loop or a family";
    let function = "inside a function that is not bound by `let` and called by its name";
    let cases = [
        (
            fam(
                set(),
                "i",
                Term::If(lit(true).into(), push(var("i")).into(), lit(0).into()),
            ),
            family,
        ),
        (fam(set(), "i", lam(&["m"], push(var("m")))), function),
        (lam(&["m"], fam(set(), "i", push(var("m")))), family),
        (
            fold(set(), lam(&["a", "b"], push(var("a"))), None),
            function,
        ),
    ];
    let wrong: Vec<String> = cases
        .iter()
        .enumerate()
        .filter_map(|(k, (t, inside))| {
            let got = lower(t).err().unwrap_or_default();
            (!got.starts_with(&refused_inside("stdout", inside))).then(|| format!("{k}: {got:?}"))
        })
        .collect();
    assert!(wrong.is_empty(), "{wrong:#?}");
}
