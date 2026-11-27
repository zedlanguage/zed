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
///
/// The corpus is dealt into [`DAMAGED_PARTS`] parts, graph `i` to part `i % DAMAGED_PARTS`, each
/// a test and so a piece of tools/run_tests.sh. As one test it took 15.5-19.9 s on a loaded hm
/// VM (FAIL-link-pieces-at-20s-limit), nearly all of it the re-check (which plans again) and
/// `zed_native::ir` of each damaged plan the read accepts; planning the two reference plans once
/// per graph instead of once per byte made no measured difference (15.9-17.7 s at load 2-15).
#[test]
fn a_damaged_plan_is_refused_in_part_0() {
    damaged_plans_are_refused(0);
}

/// Part 1 of [`a_damaged_plan_is_refused_in_part_0`].
#[test]
fn a_damaged_plan_is_refused_in_part_1() {
    damaged_plans_are_refused(1);
}

/// Part 2 of [`a_damaged_plan_is_refused_in_part_0`].
#[test]
fn a_damaged_plan_is_refused_in_part_2() {
    damaged_plans_are_refused(2);
}

/// Part 3 of [`a_damaged_plan_is_refused_in_part_0`].
#[test]
fn a_damaged_plan_is_refused_in_part_3() {
    damaged_plans_are_refused(3);
}

/// The number of parts [`a_damaged_plan_is_refused_in_part_0`] deals the corpus into: four
/// parts of 28 or 29 graphs, about a quarter of the 15.5-19.9 s each.
const DAMAGED_PARTS: usize = 4;

/// [`a_damaged_plan_is_refused_in_part_0`] on the graphs `i` of the corpus with
/// `i % DAMAGED_PARTS == part`.
fn damaged_plans_are_refused(part: usize) {
    let (mut read, mut rechecked, mut planned, mut graphs) = (0, 0, 0, 0);
    for g in corpus().iter().skip(part).step_by(DAMAGED_PARTS) {
        graphs += 1;
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
    assert!(planned <= graphs, "{planned} {graphs}");
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
    // A drop node `k` makes moved to the next node of its region, which may drop any edge
    // made before it: the bytes keep their length and every index stays in range.
    kind("a drop moved to the next node", &|d| {
        first(&|n| !n.drops.is_empty())
            .filter(|&(r, k)| k + 1 < p.regions[r].nodes.len())
            .is_some_and(|(r, k)| {
                let moved = d.regions[r].nodes[k].drops.pop().unwrap();
                d.regions[r].nodes[k + 1].drops.push(moved);
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
/// a node's inputs on a callee of more parameters). Every kind is met somewhere in each part.
///
/// The corpus is two parts, the graphs of even and of odd index, each a test and so a piece of
/// tools/run_tests.sh: as one test it took 6.1-10.7 s on a loaded hm VM
/// (FAIL-link-pieces-at-20s-limit), over the 10 s a piece is held to.
#[test]
fn each_kind_of_damage_is_refused_and_makes_no_panic_in_part_0() {
    each_kind_of_damage_is_refused(0);
}

/// Part 1 of [`each_kind_of_damage_is_refused_and_makes_no_panic_in_part_0`].
#[test]
fn each_kind_of_damage_is_refused_and_makes_no_panic_in_part_1() {
    each_kind_of_damage_is_refused(1);
}

/// [`each_kind_of_damage_is_refused_and_makes_no_panic_in_part_0`] on the graphs `i` of the
/// corpus with `i % 2 == part`.
fn each_kind_of_damage_is_refused(part: usize) {
    let mut met = std::collections::BTreeMap::<&str, (usize, usize)>::new();
    for g in corpus().iter().skip(part).step_by(2) {
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
    assert_eq!(met.len(), 11, "{met:?}");
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

/// Where the stored plan lies in an executable's program data, as `exe::data` of zed-native
/// writes it: its start and its length. The data is the 32 bytes of the program's address,
/// four texts (the ports, the limits, the file's name and its source), each its length in 8
/// bytes and then its bytes, the sites (a count, then 16 bytes each), and the plan's length
/// and bytes, which the graph follows.
fn plan_in(data: &[u8]) -> (usize, usize) {
    let n = |at: usize| {
        usize::try_from(u64::from_le_bytes(data[at..at + 8].try_into().unwrap())).unwrap()
    };
    let mut at = 32;
    for _ in 0..4 {
        at += 8 + n(at);
    }
    at += 8 + 16 * n(at);
    (at + 8, n(at))
}

/// `zedc check-exe` (plan row EXE-plan-carried-recheck) on a built executable: the file as
/// `zedc build` wrote it passes, with status 0 and nothing printed; with its stored plan
/// replaced by each damaged plan of the same length that the start reads without fault
/// ([`damaged`]: a mode flipped, a drop moved to the next node, a callee moved), the command
/// refuses it with status 1 naming the plan, and the executable still starts and runs the
/// plan as written (its start does not re-check it, by decision: `exe::check` of zed-native).
/// A file that is not an executable `zedc build` wrote, and a command line of other than one
/// file, are refused too. Negative control: the same splice of the undamaged plan passes.
#[test]
fn the_check_of_an_executable_refuses_each_damage_its_start_reads() {
    use object::{Object as _, ObjectSection as _};
    use std::process::Command;
    use zed_native::{PROGRAM_SECTION, check_command};
    let d = super::dir("check_exe");
    let src = d.join("order.zed");
    std::fs::write(
        &src,
        "main(m: MainArgs) {\n  \
         a = m.args[0] else #outOfBounds -> \"\";\n  \
         b = m.args[1] else #outOfBounds -> \"\";\n  \
         x = if a > b { \"after\" } else { \"not after\" };\n  \
         m.stdout <- \"${x}|${a}${b}\";\n}\n",
    )
    .unwrap();
    let exe = d.join("order");
    super::built(&src, &exe);
    let check = |words: &[&std::path::Path]| {
        let words: Vec<String> = words.iter().map(|w| w.to_str().unwrap().into()).collect();
        let mut stderr = Vec::new();
        let status = check_command(&words, &mut stderr);
        (status, String::from_utf8(stderr).unwrap())
    };
    assert_eq!(check(&[&exe]), (0, String::new()));
    // The plan in the file, and the graph the start reads it against.
    let bytes = std::fs::read(&exe).unwrap();
    let (at, len) = {
        let file = object::File::parse(&*bytes).unwrap();
        let s = file.section_by_name(PROGRAM_SECTION).unwrap();
        let (at, len) = s.file_range().unwrap();
        (usize::try_from(at).unwrap(), usize::try_from(len).unwrap())
    };
    let data = &bytes[at..at + len];
    let (plan_at, plan_len) = plan_in(data);
    let (graph, _) = zedc::zir::binary::decode_form(&data[plan_at + plan_len..]).unwrap();
    let start = zed_native::legalize(graph);
    let stored = Plan::from_bytes(&data[plan_at..plan_at + plan_len], start.graph()).unwrap();
    assert_eq!(stored, plan(start.graph(), stored.fuse));
    // `bytes` with the plan `p`'s bytes in place of the stored plan's, written as the
    // runnable file `name` (by `install`, in a process of its own, as `command.rs` writes a
    // runnable file, so no child another test thread forks inherits it open for writing).
    let spliced = |name: &str, p: &[u8]| {
        let mut file = bytes.clone();
        file[at + plan_at..at + plan_at + plan_len].copy_from_slice(p);
        let (staged, path) = (d.join(format!("{name}.bytes")), d.join(name));
        std::fs::write(&staged, file).unwrap();
        let installed = Command::new("install")
            .args(["-m", "755"])
            .arg(&staged)
            .arg(&path)
            .status()
            .unwrap();
        assert!(
            installed.success(),
            "install {}: {installed}",
            path.display()
        );
        path
    };
    // As `agreement.rs` runs this program: the words after `--` are `m.args`.
    let words = ["--".into(), "b".into(), "a".into()];
    let same = spliced("same", &stored.to_bytes());
    assert_eq!(check(&[&same]), (0, String::new()));
    let ran = super::executable(&same, &words, b"");
    assert_eq!((ran.status, ran.stdout.as_str()), (0, "after|ba\n"));
    let mut met = Vec::new();
    for (k, (name, p)) in damaged(start.graph(), &stored).into_iter().enumerate() {
        let b = p.to_bytes();
        if b.len() != plan_len || Plan::from_bytes(&b, start.graph()).is_err() {
            continue;
        }
        met.push(name);
        let path = spliced(&format!("damaged{k}"), &b);
        let (status, why) = check(&[&path]);
        assert_eq!(status, 1, "{name}: {why}");
        assert!(
            why.contains("memory plan is not the plan its program gives"),
            "{name}: {why}"
        );
        // The start reads the plan and runs it as written: it does not refuse the file. What
        // the run then does with a wrong plan is not checked: it may free an edge in use.
        let ran = super::executable(&path, &words, b"");
        assert!(!ran.stderr.contains("is damaged"), "{name}: {}", ran.stderr);
    }
    for name in ["a mode flipped", "a drop moved to the next node"] {
        assert!(met.contains(&name), "{name} not made: {met:?}");
    }
    // A file `zedc build` did not write, and a command line of other than one file.
    let (status, why) = check(&[&src]);
    assert_eq!(status, 1, "{why}");
    assert!(
        why.contains("is not an executable `zedc build` wrote"),
        "{why}"
    );
    let (status, why) = check(&[&d.join("missing")]);
    assert_eq!(status, 1, "{why}");
    assert!(
        why.contains("is not an executable `zedc build` wrote"),
        "{why}"
    );
    assert_eq!(check(&[]).0, 2);
    assert_eq!(check(&[&exe, &exe]).0, 2);
}
