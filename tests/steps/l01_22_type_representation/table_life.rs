//! The tables of live type nodes keep a node only while someone holds it (step TABLE-life):
//! the tables of diagram nodes, the exclusive ors and the complements of expressions, and the
//! tables of recursive groups and their instances. A long run of independent checks, each on
//! types of its own, therefore holds the same memory after `8n` checks as after `n`. A recursive
//! group's instance is a cycle of strong handles (its members' unfoldings hold the members),
//! which the end of each unit breaks (item REC-cycle).

use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

use zed_kernel::types::Type;
use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::value::Value;
use zed_tests::scaling;

/// The int literal `k` as a type.
fn lit(k: u64) -> Type {
    Type::lit(&Value::Int(k as i64)).expect("an int literal")
}

/// One independent check: tuple, morphism and union types on literals of its own (from
/// `base`), an exclusive or and complements, subtyping and emptiness, and a plain group.
fn unit(base: u64) {
    Type::forget_emptiness();
    let tuple = |k: u64| Type::tuple(vec![lit(base + k), Type::int()]);
    let (a, b) = (tuple(0), tuple(1));
    let ab = &a | &b;
    let either = &(&a - &b) | &(&b - &a);
    assert!(a.subtype(&ab) && !ab.subtype(&a));
    assert!(either.subtype(&ab) && ab.subtype(&either));
    assert!(!(!&ab).is_empty());
    let many = (2..18).fold(Type::empty(), |t, k| t | tuple(k));
    assert!(tuple(5).subtype(&many) && !a.subtype(&many));
    assert!((&many & &!&many).is_empty());
    let f = Type::exact(lit(base + 20), ab.clone());
    assert!(f.subtype(&Type::exact(lit(base + 20), Type::top())));
    assert!(!Type::exact(lit(base + 20), Type::top()).subtype(&f));
    let g = Group::new(vec![Def {
        name: format!("TableLife{base}"),
        params: vec![],
        body: Expr::Tuple(vec![Expr::Type(lit(base + 21)), Expr::Type(ab)]),
    }])
    .expect("a plain group");
    assert!(!g.instance(vec![])[0].is_empty());
}

/// One independent check on a recursive group of its own, `List = () | (k, List)` with `k`
/// from `base`: the members are unfolded by emptiness and subtyping, then dropped.
fn rec_unit(base: u64) {
    Type::forget_emptiness();
    let list = |k: u64| {
        let g = Group::new(vec![Def {
            name: format!("TableLifeList{base}"),
            params: vec![],
            body: Expr::Union(vec![
                Expr::Tuple(vec![]),
                Expr::Tuple(vec![Expr::Type(lit(base + k)), Expr::Ref(0, vec![])]),
            ]),
        }])
        .expect("a recursive group");
        g.instance(vec![]).remove(0)
    };
    let (a, b) = (list(0), list(1));
    assert!(!a.is_empty());
    assert!(a.subtype(&(&a | &b)) && !a.subtype(&b));
    assert!(Type::tuple(vec![]).subtype(&(&a & &b)));
}

/// The resident bytes of the process (`/proc/self/statm`), where Linux reports them.
fn resident() -> Option<u64> {
    let statm = std::fs::read_to_string("/proc/self/statm").ok()?;
    let pages: u64 = statm.split_whitespace().nth(1)?.parse().ok()?;
    Some(pages * 4096)
}

/// TEST-bench-move-l0123 (author P169): was n = 256 (256 + 256 + 2,048 checks, 2.5 s under
/// load); now n = 32 (32 + 32 + 256 checks). The 8n run fails when it leaves more than 4,096
/// bytes over the n run, that is over 224 more checks, so it still catches a leak of 19 bytes a
/// check, less than one table slot for each node a check makes. Measured on the code of
/// 2026-11-14, 12 runs each on a fresh thread: with no leak the 8n run leaves between -3,936 and
/// +3,936 bytes over the n run at every n from 32 to 256 alike (table capacity), so the smaller
/// n is no closer to the limit; a check that leaves one type node more leaves 299,264 bytes.
#[test]
fn a_long_run_of_independent_checks_holds_bounded_memory() {
    // Each table held every node it was given for the life of the thread, so the bytes left
    // allocated grew with the number of checks run; they now stay those of the first runs.
    // The bytes left are counted on this thread exactly (zed_alloc_count::live); the resident
    // bytes of the process are printed beside them, since the tests running beside this one
    // change those.
    let n = 32;
    let next = AtomicU64::new(1 << 40);
    let run = |count: usize| {
        let (_, live) = zed_alloc_count::live(|| {
            for _ in 0..count {
                unit(next.fetch_add(64, Relaxed));
            }
        });
        live
    };
    run(n);
    let (before, small) = (resident(), run(n));
    let (middle, large) = (resident(), run(scaling::FACTOR * n));
    let after = resident();
    eprintln!(
        "{n} checks left {} bytes, {} left {}; resident bytes {before:?}, {middle:?}, {after:?}",
        small.net,
        scaling::FACTOR * n,
        large.net
    );
    assert!(
        large.net <= small.net.max(0) + 4096,
        "{} checks left {} bytes allocated, {n} left {}",
        scaling::FACTOR * n,
        large.net,
        small.net
    );
}

/// TEST-bench-move-l0123 (author P169): was n = 256 (256 + 256 + 2,048 checks, 0.76 s under
/// load); now n = 64 (64 + 64 + 512 checks). The 8n run fails when it leaves more than 4,096
/// bytes over the n run, that is over 448 more checks, so it still catches a leak of 10 bytes a
/// check, far less than the group, members and unfoldings a check whose cycle is not broken
/// leaves. Measured on the code of 2026-11-14, 12 runs each on a fresh thread at n = 32 to 128:
/// with no leak the 8n run leaves exactly 0 bytes over the n run.
#[test]
fn a_long_run_of_checks_on_recursive_groups_holds_bounded_memory() {
    // Item REC-cycle: a recursive instance held itself, so every check on a group of its own
    // left its instance allocated for the life of the process. The end of each unit breaks
    // the cycle, so the bytes left stay those of the first runs.
    let n = 64;
    let next = AtomicU64::new(1 << 42);
    let run = |count: usize| {
        let (_, live) = zed_alloc_count::live(|| {
            for _ in 0..count {
                rec_unit(next.fetch_add(64, Relaxed));
            }
            // The last unit's instances end with the next unit.
            Type::forget_emptiness();
        });
        live
    };
    run(n);
    let small = run(n);
    let large = run(scaling::FACTOR * n);
    eprintln!(
        "{n} recursive checks left {} bytes, {} left {}",
        small.net,
        scaling::FACTOR * n,
        large.net
    );
    assert!(
        large.net <= small.net.max(0) + 4096,
        "{} recursive checks left {} bytes allocated, {n} left {}",
        scaling::FACTOR * n,
        large.net,
        small.net
    );
}

mod bench;
