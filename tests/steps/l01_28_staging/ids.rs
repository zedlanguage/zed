//! The form rule `stage::ends` knows a shared part by the id of its `Shared` node (ledger
//! TERM-id): a part held by both arms of nested `if`s is read once, the numbers it gives the
//! parts do not depend on the order the nodes were built in, and staging a unit gives the same
//! output alone as after other units.

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::sync::Arc;

use zed_kernel::term::build::{lam, lit, var};
use zed_kernel::{Prim, Shared, Term};
use zedc::elab::{Def, Unit};
use zedc::run::load;
use zedc::stage::{self, ends, reading};

fn prim(p: Prim, args: Vec<Term>) -> Term {
    Term::Prim(p, args)
}

/// `t0 = n; tj = if n >= j { t(j-1) } else { t(j-1) }`: `d` levels whose two arms are one
/// node, so `2^d` places and `2d + 1` distinct parts.
pub(super) fn same_arms(d: usize) -> Term {
    (1..=d as i64).fold(var("n"), |t, j| {
        let t = Shared::new(t);
        let guard = prim(Prim::Ge, vec![var("n"), lit(j)]);
        Term::If(Shared::new(guard), t.clone(), t)
    })
}

#[test]
fn a_part_held_by_both_arms_of_nested_ifs_is_read_once() {
    // The two arms of each `if` are one node: read by the place it is reached from, the walk
    // would take 2^d steps (`bench::ids` times 1000 and 8000 levels).
    let small = reading(&same_arms(3));
    // Per level: the guard, its two operands, and the `if`; and `n` at the bottom.
    assert_eq!(small.len(), 4 * 3 + 1);
    let top = small.last().expect("the root is read last");
    let (_, read) = top;
    assert_eq!(read.len(), 3);
    assert_eq!(read[1], read[2], "both arms are the one part read before");
    for d in [0, 1, 2, 9] {
        assert!(ends(&same_arms(d)));
        // Under a binder of `n` the chain still ends.
        let under = Term::Lam(vec!["n".into()], Shared::new(same_arms(d)));
        assert!(ends(&under));
    }
}

/// A level's parts before they are put together: the guard `n >= j + 1` and the arm
/// `t + j * 2`, whose `t` is the level below.
struct Level {
    guard: Shared,
    times: Term,
}

fn level(j: i64) -> Level {
    let bound = prim(Prim::Add, vec![lit(j), lit(1i64)]);
    Level {
        guard: Shared::new(prim(Prim::Ge, vec![var("n"), bound])),
        times: prim(Prim::Mul, vec![lit(j), lit(2i64)]),
    }
}

/// `main = (n) -> tk` with `tj = if n >= j + 1 { t(j-1) } else { t(j-1) + j * 2 }` and
/// `t0 = n`, the guards built first in the order `order` gives the levels, then the rest from
/// the bottom up. Returns the unit and the id of each level's guard and `if`, by level.
fn built(k: usize, order: impl Iterator<Item = i64>) -> (Unit, Vec<(u64, u64)>) {
    let mut levels: BTreeMap<i64, Level> = order.map(|j| (j, level(j))).collect();
    let mut ids = Vec::new();
    let mut t = Shared::new(var("n"));
    for j in 1..=k as i64 {
        let Level { guard, times } = levels.remove(&j).expect("each level built once");
        let plus = Shared::new(prim(Prim::Add, vec![(*t).clone(), times]));
        let next = Shared::new(Term::If(guard.clone(), t, plus));
        ids.push((guard.id(), next.id()));
        t = next;
    }
    let main = Shared::new(Term::Lam(vec!["n".into()], t));
    let def = Def {
        name: "main".into(),
        kernel: "main".into(),
        term: main,
        first_order: false,
    };
    let unit = Unit {
        defs: vec![def],
        tests: Arc::from([]),
        warnings: Vec::new(),
        int_params: Default::default(),
        limits: Default::default(),
    };
    (unit, ids)
}

/// Where each id falls among the others.
fn ranks(ids: &[u64]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..ids.len()).collect();
    order.sort_by_key(|&i| ids[i]);
    order
}

#[test]
fn two_build_orders_read_and_stage_alike() {
    let k = 12;
    let (up, up_ids) = built(k, 1..=k as i64);
    let (down, down_ids) = built(k, (1..=k as i64).rev());
    // The nodes' ids follow the order they were built in, so the two builds order them apart.
    let all = |ids: &[(u64, u64)]| ids.iter().flat_map(|&(g, i)| [g, i]).collect::<Vec<_>>();
    assert_ne!(ranks(&all(&up_ids)), ranks(&all(&down_ids)));
    let (a, b) = (&up.defs[0].term, &down.defs[0].term);
    assert_eq!(a, b, "the same term");
    // The reading numbers the parts the same way and gives the same answers.
    let first = reading(a);
    // Per level: the guard (5 parts), the arm (5, its copy of the level below one part, the
    // nodes under that copy read before) and the `if`; and `n` and the lambda.
    assert_eq!(first.len(), 11 * k + 2);
    assert_eq!(reading(b), first);
    assert!(ends(a) && ends(b));
    // The staged unit is the same: each `j + 1` and `j * 2` evaluated by the build.
    let (staged_up, report_up) = stage::mix(&up, &["main"]);
    let (staged_down, report_down) = stage::mix(&down, &["main"]);
    let printed = |u: &Unit| u.defs[0].term.to_string();
    assert_eq!(printed(&staged_up), printed(&staged_down));
    assert_eq!(report_up, report_down);
    assert_ne!(
        printed(&staged_up),
        printed(&up),
        "the build evaluated the constants"
    );
    assert!(!printed(&staged_up).contains('*'));
}

/// Every unit of the corpus and of the steps' tests that loads, and programs with build-stage
/// constants, a chain of `if`s, a local function called at build, a call the build does not
/// run, and a definition nothing reads.
fn units() -> Vec<(String, Vec<u8>)> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut dirs = vec![root.join("../zed/corpus")];
    for step in std::fs::read_dir(root.join("steps")).unwrap() {
        dirs.push(step.unwrap().path().join("zed"));
    }
    let mut out = Vec::new();
    for dir in dirs {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for path in entries.map(|e| e.unwrap().path()) {
            if path.extension().is_some_and(|x| x == "zed") {
                out.push((path.display().to_string(), std::fs::read(&path).unwrap()));
            }
        }
    }
    out.sort();
    // The files of later layers do not load yet; every program written below does.
    out.retain(|(_, src)| load(src).is_ok());
    let mut chain = String::from("main(m: MainArgs) {\n  x0 = int(m.stdin[0]) else 0;\n");
    for i in 1..=40 {
        chain += &format!(
            "  x{i} = if x{} >= {i} {{ x{} }} else {{ x{} + {i} * 2 }};\n",
            i - 1,
            i - 1,
            i - 1
        );
    }
    chain += "  m.stdout <- String(x40);\n}\n";
    out.extend([
        (
            "a log filter".into(),
            b"day = 60 * 60 * 24;\nweek = 7 * day;\nmain(m: MainArgs) {\n  secs = int(m.stdin[0]) else 0;\n  m.stdout <- String(week - secs) ++ \" left of \" ++ String(week);\n}\n".to_vec(),
        ),
        ("a chain of ifs".into(), chain.into_bytes()),
        (
            "a local function called at build".into(),
            b"main(m: MainArgs) {\n  add(a: int, b: int) = a + b;\n  k = add(a: add(a: 1, b: 2), b: 3);\n  m.stdout <- String(k);\n}\n".to_vec(),
        ),
        (
            "a call the build does not run".into(),
            b"w(positional f) = f(f);\nspin = w(w);\nmain(m: MainArgs) {\n  m.stdout <- if false { String(spin) } else { \"x\" };\n}\n".to_vec(),
        ),
        (
            "a definition nothing reads".into(),
            b"whole(positional v: int) = v;\nbroken = 1 div whole(0);\nunused = broken + 1;\nmain(m: MainArgs) {\n  m.stdout <- \"a\" ++ \"b\";\n}\n".to_vec(),
        ),
    ]);
    out
}

/// `src` staged: each definition printed, and the report.
fn staged(src: &[u8]) -> String {
    let (p, report) = load(src).expect("loaded before").stage();
    let defs: Vec<String> = p
        .unit()
        .defs
        .iter()
        .map(|d| format!("{} = {}", d.name, d.term))
        .collect();
    format!("{}\n{report:?}", defs.join("\n"))
}

#[test]
fn staging_a_unit_alone_and_after_others_agree() {
    // Ids are drawn from one source in the order nodes are built, so a unit staged after
    // others has larger ids than staged alone; its staged output must not change.
    let units = units();
    assert!(units.len() >= 9, "{} units", units.len());
    let alone: Vec<String> = units
        .iter()
        .map(|(_, src)| {
            let src = src.clone();
            std::thread::spawn(move || staged(&src)).join().unwrap()
        })
        .collect();
    let srcs: Vec<Vec<u8>> = units.iter().map(|(_, s)| s.clone()).collect();
    let forward = {
        let srcs = srcs.clone();
        std::thread::spawn(move || srcs.iter().map(|s| staged(s)).collect::<Vec<_>>())
    };
    let backward = std::thread::spawn(move || {
        let mut out: Vec<String> = srcs.iter().rev().map(|s| staged(s)).collect();
        out.reverse();
        out
    });
    let (forward, backward) = (forward.join().unwrap(), backward.join().unwrap());
    for (i, (name, _)) in units.iter().enumerate() {
        assert_eq!(
            forward[i], alone[i],
            "{name}: staged after the units before it"
        );
        assert_eq!(
            backward[i], alone[i],
            "{name}: staged after the units after it"
        );
    }
}

#[test]
fn a_shared_part_with_a_fix_does_not_end_at_any_place() {
    // The bottom of the chain is a `fix`: every one of the 2^d places reaches it, and the
    // answer read once for the shared part holds for all of them.
    let d = 40;
    let bottom = Term::Fix {
        init: Shared::new(lit(0i64)),
        step: Shared::new(lam(&["x"], var("x"))),
        this: "this".into(),
        key: "key".into(),
        kind: zed_kernel::FixKind::Definedness,
        ev: Default::default(),
    };
    let t = (1..=d as i64).fold(bottom, |t, j| {
        let t = Shared::new(t);
        let guard = prim(Prim::Ge, vec![var("n"), lit(j)]);
        Term::If(Shared::new(guard), t.clone(), t)
    });
    assert!(!ends(&t));
    assert_eq!(reading(&t).len(), 4 * d + 1);
}
