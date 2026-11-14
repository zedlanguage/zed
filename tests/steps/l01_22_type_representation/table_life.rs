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

/// After `n` independent checks to fill the tables, `8n` more leave no more bytes allocated on
/// this thread than `n` more, within 4,096 bytes of table capacity.
fn independent_checks_hold_bounded_memory(n: usize) {
    // Each table held every node it was given for the life of the thread, so the bytes left
    // allocated grew with the number of checks run; they now stay those of the first runs.
    // The bytes left are counted on this thread exactly (zed_alloc_count::live); the resident
    // bytes of the process are printed beside them, since the tests running beside this one
    // change those.
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

/// After `n` checks on recursive groups of their own, `8n` more leave no more bytes allocated
/// on this thread than `n` more, within 4,096 bytes.
fn recursive_checks_hold_bounded_memory(n: usize) {
    // Item REC-cycle: a recursive instance held itself, so every check on a group of its own
    // left its instance allocated for the life of the process. The end of each unit breaks
    // the cycle, so the bytes left stay those of the first runs.
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

/// Small instance of `bench::a_long_run_of_independent_checks_holds_bounded_memory`
/// (TEST-bench-move-l0123, author P178: a long run is a benchmark): n = 4, so 4 + 4 + 32
/// checks. The 32 checks fail the test when they leave more than 4,096 bytes over the 4, that
/// is a leak of over 147 bytes a check, less than the 1,336 bytes a check that leaves one type
/// node more leaves (299,264 bytes over 224 checks, measured at n = 32).
#[test]
fn independent_checks_release_their_nodes() {
    independent_checks_hold_bounded_memory(4);
}

/// Small instance of `bench::a_long_run_of_checks_on_recursive_groups_holds_bounded_memory`
/// (TEST-bench-move-l0123, author P178): n = 4, so 4 + 4 + 32 checks. The 32 checks fail the
/// test when they leave more than 4,096 bytes over the 4, a leak of over 147 bytes a check,
/// less than the group, members and unfoldings a check whose cycle is not broken leaves.
#[test]
fn checks_on_recursive_groups_release_their_instances() {
    recursive_checks_hold_bounded_memory(4);
}

/// Tuple, union, complement, morphism and recursive-group types on literals from `base`, each
/// with a node in one of the thread's tables (rows, morphism types, diagram nodes, groups).
fn kept(base: u64) -> Vec<Type> {
    let tuple = |k: u64| Type::tuple(vec![lit(base + k), Type::int()]);
    let (a, b) = (tuple(0), tuple(1));
    let ab = &a | &b;
    let list = Group::new(vec![Def {
        name: format!("TableLifeKept{base}"),
        params: vec![],
        body: Expr::Union(vec![
            Expr::Tuple(vec![]),
            Expr::Tuple(vec![Expr::Type(lit(base + 2)), Expr::Ref(0, vec![])]),
        ]),
    }])
    .expect("a recursive group")
    .instance(vec![])
    .remove(0);
    vec![
        a.clone(),
        b,
        !&ab,
        Type::exact(lit(base + 3), ab.clone()),
        ab,
        list,
    ]
}

/// `got` holds the types of [`kept`]`(base)`, made on this thread or another: each equals the
/// one made here, and the subtyping and emptiness among them hold.
fn check_kept(base: u64, got: &[Type]) {
    Type::forget_emptiness();
    let here = kept(base);
    assert_eq!(got, &here[..]);
    let [a, b, not_ab, f, ab, list] = got else {
        panic!("six types")
    };
    assert!(a.subtype(ab) && b.subtype(ab) && !ab.subtype(a));
    assert!((ab & not_ab).is_empty() && !not_ab.is_empty());
    assert!(f.subtype(&Type::exact(lit(base + 3), Type::top())));
    assert!(!list.is_empty() && Type::tuple(vec![]).subtype(list));
    assert!(!list.subtype(&here[0]));
}

/// Types made on one thread and dropped on another (TEST-bench-move-l0123, author P188: before,
/// only the benchmarks, each of whose runs is on a thread of its own, dropped a node where the
/// thread's table does not hold it). A node made on a thread that has ended is dropped here,
/// after that thread's tables are gone; a node made here is dropped on a thread that is still
/// running, whose tables hold no entry for it. Afterward both threads build equal types, and
/// subtyping and emptiness on them still hold.
#[test]
fn types_dropped_on_another_thread_leave_both_threads_correct() {
    let made_there = std::thread::spawn(|| {
        let made = kept(0);
        check_kept(0, &made);
        made
    })
    .join()
    .expect("the thread that made the types");
    check_kept(0, &made_there);
    drop(made_there);
    check_kept(0, &kept(0));

    let made_here = kept(100);
    check_kept(100, &made_here);
    std::thread::spawn(move || {
        let own = kept(100);
        check_kept(100, &made_here);
        drop(made_here);
        check_kept(100, &own);
        check_kept(100, &kept(100));
    })
    .join()
    .expect("the thread that dropped the types");
    check_kept(100, &kept(100));
}

mod bench;
