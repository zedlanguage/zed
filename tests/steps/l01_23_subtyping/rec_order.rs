//! Deterministic checking with recursive types (repair REC-id-order): the digest and the order
//! of a recursive type follow its group's definitions, its member and its arguments, never
//! how many recursive types the process made before it. One program's types are built in a
//! child process alone, and in another child after a different program built recursive types
//! of its own first; the digests, the order of the types, their printed text and every
//! verdict must agree.

use std::collections::BTreeSet;
use std::hash::{Hash, Hasher};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_tests::scaling;

/// Set in a child process to `alone` or `after`.
const CHILD: &str = "ZED_REC_ORDER_CHILD";

fn def(name: &str, body: Expr) -> Def {
    Def {
        name: name.into(),
        params: vec![],
        body,
    }
}

fn atom(name: &str, items: Vec<Expr>) -> Expr {
    Expr::Atom(name.into(), items)
}

fn bare(name: &str) -> Expr {
    Expr::Type(Type::atom(name))
}

/// The lists of integers, each cell the atom `cell`, whose length is `k` modulo `p`.
fn period(cell: &str, p: usize, k: usize) -> Type {
    periods(cell, p, k).remove(0)
}

/// The members of [`period`]'s group: member `i` is the lists of length `k - i` modulo `p`.
fn periods(cell: &str, p: usize, k: usize) -> Vec<Type> {
    let defs = (0..p)
        .map(|i| {
            let cons = atom(
                cell,
                vec![Expr::Type(Type::int()), Expr::Ref((i + 1) % p, vec![])],
            );
            let body = match i == k {
                true => Expr::Union(vec![bare("nil"), cons]),
                false => cons,
            };
            def(&format!("{cell}{p}_{i}"), body)
        })
        .collect();
    Group::new(defs).unwrap().instance(vec![])
}

/// The program checked: lists of periodic lengths, a list whose tail is written as a union
/// (`type S = #node(int, S | #nil)`, a part kept unevaluated), and two definitions recursive
/// with each other through such parts.
fn program() -> Vec<Type> {
    let mut ts: Vec<Type> = [(1, 0), (2, 0), (2, 1), (3, 0), (3, 2), (4, 1), (6, 5)]
        .into_iter()
        .map(|(p, k)| period("cons", p, k))
        .collect();
    let s = Group::new(vec![def(
        "S",
        atom(
            "node",
            vec![
                Expr::Type(Type::int()),
                Expr::Union(vec![Expr::Ref(0, vec![]), bare("nil")]),
            ],
        ),
    )])
    .unwrap()
    .instance(vec![]);
    ts.extend(s);
    let even_odd = Group::new(vec![
        def(
            "Even",
            Expr::Union(vec![
                bare("z"),
                atom(
                    "s",
                    vec![Expr::Union(vec![Expr::Ref(1, vec![]), bare("x")])],
                ),
            ]),
        ),
        def(
            "Odd",
            atom(
                "s",
                vec![Expr::Union(vec![Expr::Ref(0, vec![]), bare("y")])],
            ),
        ),
    ])
    .unwrap()
    .instance(vec![]);
    ts.extend(even_odd);
    ts
}

/// Another program, checked first in the `after` child: recursive types of other names.
fn other_program() {
    for p in 1..=9 {
        for k in 0..p {
            let t = period("other", p, k);
            assert!(!t.is_empty());
        }
    }
}

/// What the program's checking shows, one line per fact: each type's digest (by the hash of
/// `Type`, which is its digest), the order of the types, their text, and the verdicts of
/// unions, differences and pairs of them.
fn report(ts: &[Type]) -> Vec<String> {
    let mut out = Vec::new();
    for (i, t) in ts.iter().enumerate() {
        let mut h = std::hash::DefaultHasher::new();
        t.hash(&mut h);
        out.push(format!("digest {i} {:016x}", h.finish()));
    }
    let sorted: BTreeSet<(Type, usize)> = ts.iter().cloned().zip(0..).collect();
    let order: Vec<usize> = sorted.into_iter().map(|(_, i)| i).collect();
    out.push(format!("order {order:?}"));
    for (i, t) in ts.iter().enumerate() {
        out.push(format!("text {i} {t}"));
    }
    let tuples = Type::union_all(ts.iter().map(|t| Type::tuple(vec![t.clone()])));
    out.push(format!("union {tuples}"));
    for (i, a) in ts.iter().enumerate() {
        for (j, b) in ts.iter().enumerate() {
            let pair = Type::tuple(vec![a.clone(), b.clone()]);
            let swapped = Type::tuple(vec![b.clone(), a.clone()]);
            out.push(format!(
                "verdict {i} {j} {:?} {:?} {:?}",
                (a - b).verdict(),
                (&(a | b) - &tuples).verdict(),
                (&pair - &swapped).verdict(),
            ));
        }
    }
    out
}

/// In a child, prints the report between markers and returns `None`; in the parent, runs the
/// child in `mode` and returns its report.
fn child(mode: &str) -> Option<Vec<String>> {
    if let Some(m) = std::env::var_os(CHILD) {
        if m == "after" {
            other_program();
        }
        for line in report(&program()) {
            println!("REPORT {line}");
        }
        return None;
    }
    let name = format!(
        "{}::checking_a_program_alone_or_after_another_agrees",
        module_path!()
            .strip_prefix("steps::")
            .unwrap_or(module_path!())
    );
    let out = Command::new(std::env::current_exe().expect("the test binary has a path"))
        .args(["--exact", &name, "--nocapture", "--test-threads=1"])
        .env(CHILD, mode)
        .output()
        .expect("the test binary runs");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success() && stdout.contains("1 passed"),
        "{name} in the child `{mode}`: {}\n{stdout}\n{}",
        out.status,
        String::from_utf8_lossy(&out.stderr)
    );
    Some(
        stdout
            .lines()
            .filter_map(|l| l.strip_prefix("REPORT "))
            .map(String::from)
            .collect(),
    )
}

#[test]
fn checking_a_program_alone_or_after_another_agrees() {
    let Some(alone) = child("alone") else { return };
    let after = child("after").expect("the parent runs the child");
    assert!(
        alone.len() > 100,
        "the child reported {} lines",
        alone.len()
    );
    let differ: Vec<String> = alone
        .iter()
        .zip(&after)
        .filter(|(a, b)| a != b)
        .map(|(a, b)| format!("alone: {a}\nafter: {b}"))
        .collect();
    assert!(
        differ.is_empty() && alone.len() == after.len(),
        "{} of {} lines differ:\n{}",
        differ.len(),
        alone.len(),
        differ.join("\n")
    );
}

#[test]
fn the_members_of_a_group_are_ordered_in_n_log_n() {
    // Input Θ(n): a group of n definitions. Its n members are built, sorted and their 1-tuples
    // united; each comparison of two members is decided by their keys, so the order costs
    // O(n log n) comparisons of constant cost, and the whole O(n log n).
    std::thread::scope(|s| {
        std::thread::Builder::new()
            .stack_size(1 << 28)
            .spawn_scoped(s, || {
                let tag = AtomicUsize::new(0);
                scaling::check(
                    "a group's members, built, sorted and united, by n",
                    512,
                    |n| {
                        let cell = format!("scale{}", tag.fetch_add(1, Relaxed));
                        let ts = periods(&cell, n, 0);
                        let sorted: BTreeSet<&Type> = ts.iter().collect();
                        assert_eq!(sorted.len(), n);
                        let u = Type::union_all(ts.iter().map(|t| Type::tuple(vec![t.clone()])));
                        assert!(!u.is_empty());
                    },
                );
            })
            .unwrap()
            .join()
            .unwrap()
    });
}
