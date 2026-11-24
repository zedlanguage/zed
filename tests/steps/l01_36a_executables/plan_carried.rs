//! The memory plan an executable carries (plan row EXE-plan-carried; DESIGN.md sec:kernel,
//! "Facts carried, and the stripped form": no runtime works a fact out again). The build
//! stores the plan its code was made from, and the start reads it, checked against the graph,
//! instead of planning again; `Plan::recheck` plans again and compares.
//!
//! The corpus is the graph of each closed term the runner evaluates over the step units, as
//! `l01_36_cranelift::corpus` runs them natively: 115 graphs.

use std::cell::RefCell;

use zed_kernel::{Evaluator, Term};
use zed_tests::oracle::step_units;
use zedc::testing::test_through;
use zedc::zir::lower::lower;
use zedc::zir::memory::{Mode, NodePlan, Plan, plan};
use zedc::zir::{Region, Src};

/// The lowered graph of each closed term the runner evaluates over the step units.
pub(super) fn corpus() -> Vec<Region> {
    let graphs = RefCell::new(Vec::new());
    let through = |t: &Term, ev: &mut Evaluator| {
        let g = lower(t)?;
        graphs.borrow_mut().push(g.clone());
        let g = zed_native::legalize(g);
        zed_native::run(&g, &plan(g.graph(), true), ev).map(|o| o.value)
    };
    for path in step_units() {
        let text = std::fs::read_to_string(&path).unwrap();
        test_through(&text, &through);
    }
    graphs.into_inner()
}

/// The graph the start of an executable runs: `g` in the stripped form the executable holds,
/// read back and legalized.
pub(super) fn at_start(g: &Region) -> zedc::zir::legalize::Legalized {
    let bytes = zedc::zir::strip::encode_stripped(g).unwrap();
    let (read, _) = zedc::zir::binary::decode_form(&bytes).unwrap();
    zed_native::legalize(read)
}

#[test]
fn the_stored_plan_is_the_plan_worked_out_again_on_the_corpus() {
    let corpus = corpus();
    assert_eq!(corpus.len(), 115);
    for fuse in [true, false] {
        for g in &corpus {
            // What the build stores: the plan of the full graph legalized.
            let built = plan(zed_native::legalize(g.clone()).graph(), fuse);
            let start = at_start(g);
            let read = Plan::from_bytes(&built.to_bytes(), start.graph()).unwrap();
            assert_eq!(read, built);
            assert_eq!(read.recheck(start.graph()), Ok(()));
        }
    }
}

/// Each byte of each stored plan of the corpus changed in turn: the read refuses it, or the
/// re-check does, and neither the read nor making the tables and code from what was read
/// panics. A change that leaves a plan the planner makes is no damage: byte 0 is `fuse`, and
/// with it changed the bytes hold `plan(g, false)` exactly, which is kept and runs correctly,
/// without fusing.
#[test]
fn a_damaged_plan_is_refused() {
    let (mut read, mut rechecked, mut planned) = (0, 0, 0);
    for g in &corpus() {
        let start = at_start(g);
        let bytes = plan(start.graph(), true).to_bytes();
        for at in 0..bytes.len() {
            let mut damaged = bytes.clone();
            damaged[at] ^= 1;
            let Ok(p) = Plan::from_bytes(&damaged, start.graph()) else {
                read += 1;
                continue;
            };
            if p == plan(start.graph(), p.fuse) {
                planned += 1;
                continue;
            }
            let refused = p.recheck(start.graph());
            assert!(refused.is_err(), "byte {at} changed, and the plan was kept");
            rechecked += 1;
            // What a start would make of it: an error or tables, never a panic.
            let _ = zed_native::ir(&start, &p);
        }
    }
    // Both checks refuse some: the read the counts and indices, the re-check the rest. Only the
    // change of `fuse` leaves a plan the planner makes, one for each graph.
    assert!(read > 0 && rechecked > 0, "{read} {rechecked}");
    assert!(planned <= 115, "{planned}");
}

/// The kinds of damage that keep every count and index of a plan in range, each made on the
/// plan of graph `g` where the plan has a place for it: what the read of the bytes alone
/// cannot see from their lengths. Each is named for the test's message.
fn damaged(g: &Region, p: &Plan) -> Vec<(&'static str, Plan)> {
    let mut out = Vec::new();
    let mut kind = |name, f: &dyn Fn(&mut Plan) -> bool| {
        let mut d = p.clone();
        if f(&mut d) {
            out.push((name, d));
        }
    };
    // Each node of each region, as (region, node).
    let nodes: Vec<(usize, usize)> = (p.regions.iter().enumerate())
        .flat_map(|(r, rp)| (0..rp.nodes.len()).map(move |k| (r, k)))
        .collect();
    let first = |test: &dyn Fn(&NodePlan) -> bool| {
        nodes
            .iter()
            .copied()
            .find(|&(r, k)| test(&p.regions[r].nodes[k]))
    };
    kind("a mode flipped", &|d| {
        first(&|n| !n.modes.is_empty()).is_some_and(|(r, k)| {
            let m = &mut d.regions[r].nodes[k].modes[0];
            *m = if *m == Mode::Owned {
                Mode::Borrowed
            } else {
                Mode::Owned
            };
            true
        })
    });
    kind("a dup added", &|d| {
        first(&|n| !n.modes.is_empty()).is_some_and(|(r, k)| {
            d.regions[r].nodes[k].dups.push(0);
            true
        })
    });
    kind("a drop removed", &|d| {
        first(&|n| !n.drops.is_empty()).is_some_and(|(r, k)| {
            d.regions[r].nodes[k].drops.pop();
            true
        })
    });
    kind("a last use removed", &|d| {
        first(&|n| !n.last.is_empty()).is_some_and(|(r, k)| {
            d.regions[r].nodes[k].last.pop();
            true
        })
    });
    // In the root region, whose graph is `g`: node 0 drops, or is the last use of, an output
    // of the last node, or of itself.
    let later = (g.nodes.len() > 1 && g.nodes.iter().all(|n| !n.outputs.is_empty()))
        .then(|| g.nodes.len() - 1);
    kind("a drop of a later node's output", &|d| {
        later.is_some_and(|m| {
            d.regions[0].nodes[0].drops.push(Src::Out(m, 0));
            true
        })
    });
    kind("a last use of the node's own output", &|d| {
        later.is_some_and(|_| {
            d.regions[0].nodes[0].last.push(Src::Out(0, 0));
            true
        })
    });
    // A region's plan has a mode for each of its arguments.
    kind("an entry drop added", &|d| {
        let at = p.regions.iter().position(|rp| !rp.args.is_empty());
        at.map(|r| d.regions[r].entry_drops.push(0)).is_some()
    });
    kind("a result dup added", &|d| {
        (!g.results.is_empty())
            .then(|| d.regions[0].result_dups.push(0))
            .is_some()
    });
    // The callees the plan sees, and a callee moved to another of them, or to the root
    // region, which is no lambda's body.
    let callees: Vec<usize> = nodes
        .iter()
        .filter_map(|&(r, k)| p.regions[r].nodes[k].callee)
        .collect();
    kind("a callee moved to another lambda", &|d| {
        let other = |c: usize| callees.iter().copied().find(|&o| o != c);
        first(&|n| n.callee.is_some_and(|c| other(c).is_some())).is_some_and(|(r, k)| {
            let n = &mut d.regions[r].nodes[k];
            n.callee = n.callee.and_then(other);
            true
        })
    });
    kind("a callee moved to a region no lambda has", &|d| {
        first(&|n| n.callee.is_some()).is_some_and(|(r, k)| {
            d.regions[r].nodes[k].callee = Some(0);
            true
        })
    });
    out
}

/// Each kind of damage that keeps the plan's counts and indices in range ([`damaged`]), made on
/// each plan of the corpus: the read refuses it or the re-check does, and making the tables and
/// code from what was read gives code or an error, never a panic (risk named by b22-small12:
/// `zed_native::ir` indexed past a node's outputs on a drop of a later node's output, and past
/// a node's inputs on a callee of more parameters). Every kind is met somewhere in the corpus.
#[test]
fn each_kind_of_damage_is_refused_and_makes_no_panic() {
    let mut met = std::collections::BTreeMap::<&str, (usize, usize)>::new();
    for g in &corpus() {
        let start = at_start(g);
        let p = plan(start.graph(), true);
        for (name, d) in damaged(start.graph(), &p) {
            let counts = met.entry(name).or_default();
            let Ok(read) = Plan::from_bytes(&d.to_bytes(), start.graph()) else {
                counts.0 += 1;
                continue;
            };
            counts.1 += 1;
            // A damage that leaves the plan one the planner makes is no damage.
            if read == p {
                continue;
            }
            assert!(read.recheck(start.graph()).is_err(), "{name}: kept");
            let made = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                zed_native::ir(&start, &read).map(|_| ())
            }));
            assert!(made.is_ok(), "{name}: making code from it panicked");
        }
    }
    // (refused when read, read and refused by the re-check), by kind.
    assert_eq!(met.len(), 10, "{met:?}");
    for name in [
        "a drop of a later node's output",
        "a last use of the node's own output",
    ] {
        assert_eq!(met[name].1, 0, "{name}: read, {met:?}");
    }
}

/// A plan whose `apply` names a lambda of other arity as its callee makes no direct call to
/// it: the tables leave the call to the runtime, which checks the arity, so the code does not
/// read a mode for a parameter the node has no input for.
#[test]
fn a_callee_of_another_arity_makes_no_direct_call() {
    use zed_kernel::term::build::{app, lam, let_, lit, var};
    // `f = x -> x; g = (x, y) -> x; f("a") > g("a", "b")`: two lambdas, of 1 and 2 parameters.
    // Each is bound by a `let`, since a literal lambda applied to as many arguments as it has
    // parameters is lowered in place, with no `apply` (`zir::lower`, `apply`).
    let one = app(var("f"), vec![lit("a")]);
    let two = app(var("g"), vec![lit("a"), lit("b")]);
    let body = zed_kernel::term::build::prim(zed_kernel::term::Prim::Gt, vec![one, two]);
    let term = let_(
        "f",
        lam(&["x"], var("x")),
        let_("g", lam(&["x", "y"], var("x")), body),
    );
    let g = lower(&term).unwrap();
    let start = at_start(&g);
    let p = plan(start.graph(), true);
    let calls: Vec<(usize, usize, usize)> = (p.regions.iter().enumerate())
        .flat_map(|(r, rp)| {
            (rp.nodes.iter().enumerate()).filter_map(move |(k, n)| n.callee.map(|c| (r, k, c)))
        })
        .collect();
    assert_eq!(calls.len(), 2, "{calls:?}");
    // Each call names the other's lambda.
    let mut d = p.clone();
    d.regions[calls[0].0].nodes[calls[0].1].callee = Some(calls[1].2);
    d.regions[calls[1].0].nodes[calls[1].1].callee = Some(calls[0].2);
    let read = Plan::from_bytes(&d.to_bytes(), start.graph()).unwrap();
    assert!(read.recheck(start.graph()).is_err());
    let made = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        zed_native::ir(&start, &read).map(|_| ())
    }));
    assert!(made.is_ok(), "making code from it panicked");
}

/// Cut short anywhere, a stored plan is refused, naming the byte where it ends.
#[test]
fn a_plan_cut_short_is_refused() {
    let g = lower(&zed_kernel::term::build::lit("a")).unwrap();
    let start = at_start(&g);
    let bytes = plan(start.graph(), false).to_bytes();
    for cut in 0..bytes.len() {
        let e = Plan::from_bytes(&bytes[..cut], start.graph()).unwrap_err();
        assert!(e.contains("of the memory plan"), "{e}");
    }
    let mut longer = bytes.clone();
    longer.push(0);
    let e = Plan::from_bytes(&longer, start.graph()).unwrap_err();
    assert!(e.contains("bytes follow the plan"), "{e}");
}
