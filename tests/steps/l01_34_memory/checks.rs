//! The machine's checks fail on a wrong plan: a missed drop, an extra dup, a missing dup and
//! a borrowed argument given to a parameter that consumes it are each reported, with the
//! node and the edge.

use zed_kernel::Prim;
use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zedc::zir::memory::Mode;

use super::{cat, planned, run};

fn reads_twice() -> zed_kernel::Term {
    let_(
        "s",
        cat("ab", "c"),
        prim(
            Prim::Tuple,
            vec![
                prim(Prim::Len, vec![var("s")]),
                prim(Prim::Upper, vec![var("s")]),
            ],
        ),
    )
}

#[test]
fn a_missed_drop_is_a_leak() {
    let (g, mut p) = planned(&reads_twice(), true);
    p.regions.get_mut("r").unwrap().nodes[2].drops.clear();
    let e = run(&g, &p).unwrap_err();
    assert_eq!(
        e,
        "memory: r.2: edge 0.0 is still owned after its last use, a leak"
    );
}

#[test]
fn an_extra_dup_is_a_count_above_its_references() {
    let (g, mut p) = planned(&reads_twice(), true);
    p.regions.get_mut("r").unwrap().nodes[1].dups.push(0);
    let e = run(&g, &p).unwrap_err();
    assert!(
        e.starts_with("memory: at node r.1, cell 0 has count 2 and 1 reference"),
        "{e}"
    );
}

#[test]
fn a_missing_dup_consumes_an_edge_twice() {
    let t = let_(
        "s",
        cat("ab", "c"),
        prim(Prim::Tuple, vec![var("s"), var("s")]),
    );
    let (g, mut p) = planned(&t, true);
    p.regions.get_mut("r").unwrap().nodes[1].dups.clear();
    let e = run(&g, &p).unwrap_err();
    assert_eq!(
        e,
        "memory: r.1: input 1, taken owned consumes edge 0.0, already consumed or past its \
         last use"
    );
}

#[test]
fn a_borrowed_argument_to_a_consuming_parameter_is_refused() {
    let g = lam(&["x"], prim(Prim::Tuple, vec![var("x"), lit(1)]));
    let t = let_("g", g, app(var("g"), vec![cat("a", "b")]));
    let (g, mut p) = planned(&t, true);
    p.regions.get_mut("r").unwrap().nodes[2].modes[1] = Mode::Borrowed;
    let e = run(&g, &p).unwrap_err();
    assert_eq!(
        e,
        "memory: r.2: argument 0 is passed borrowed to `r.0/0`, which consumes it"
    );
}
