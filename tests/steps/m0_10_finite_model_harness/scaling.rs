//! The definedness `fix` at the rule of low complexity (DESIGN.md Part G). Each attempt at an
//! entry reads the family defined so far; copying the domain and that family into every
//! attempt made a `fix` over `D` keys cost `O(D²)` even when each entry is tried at most twice.
//! An entry postponed on an undefined key waits on it, so a chain, such as the accumulators of
//! a `foldl`, costs `D` attempts under every schedule rather than `D²/2` in rounds.

use zed_kernel::term::build::if_;
use zed_kernel::term::build::lit;
use zed_kernel::{Evaluator, Family, Schedule, Term, Value, World};
use zed_tests::kernel::*;
use zed_tests::scaling;

/// The family `k -> k` over `0..d`, each entry above 0 reading entry 0 (`star`) or the entry
/// before it (`chain`).
fn counts(d: usize, chain: bool) -> Term {
    let keys = lit(Value::Family(Family::set(0..d as i64)));
    fix_defined(keys, |this, k| {
        let from = if chain {
            sub(k.clone(), lit(1))
        } else {
            lit(0)
        };
        let step = if chain { lit(1) } else { k.clone() };
        if_(eq(k, lit(0)), lit(0), add(get(this, from), step))
    })
}

fn run(t: &Term, schedule: Schedule) -> Value {
    Evaluator::new(World::new())
        .with_schedule(schedule)
        .run(t)
        .unwrap()
}

#[test]
fn the_definedness_fix_scales() {
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            // Two rounds: every entry but 0 is postponed once.
            scaling::check("rounds, entries reading entry 0, by keys", 1000, |d| {
                run(&counts(d, false), Schedule::Rounds);
            });
            scaling::check("chaotic, entries reading entry 0, by keys", 1000, |d| {
                run(&counts(d, false), Schedule::Chaotic(7));
            });
            // Each entry waits on, or demands, the one before it.
            for schedule in [Schedule::Rounds, Schedule::Chaotic(7), Schedule::Pull] {
                scaling::check(&format!("{schedule:?}, a chain, by keys"), 1000, |d| {
                    run(&counts(d, true), schedule);
                });
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn every_schedule_defines_the_counts() {
    let want = |d: usize| {
        Value::Family(
            Family::from_leaves((0..d as i64).map(|k| (vec![Value::Int(k)], Value::Int(k))))
                .unwrap(),
        )
    };
    for chain in [false, true] {
        for schedule in [Schedule::Rounds, Schedule::Pull, Schedule::Chaotic(3)] {
            assert_eq!(
                run(&counts(50, chain), schedule),
                want(50),
                "{schedule:?}, chain {chain}"
            );
        }
    }
}

#[test]
fn a_jacobi_round_reads_the_family_as_the_round_began() {
    // Each round is one unit of fuel. A chain of 40 entries defines one entry per round, so
    // it takes 40 rounds and a 41st that finds nothing left; a round that read the entries
    // defined earlier in the same round would define the whole chain in one.
    let chain = counts(40, true);
    let with = |fuel| Evaluator::new(World::new()).with_fuel(fuel).run(&chain);
    assert!(with(40).is_err(), "40 rounds do not finish a chain of 40");
    assert!(with(41).is_ok());
}

/// The family over `0..d` whose entry 0 sums the entries `1..d`, each `k` itself.
fn fan_in(d: usize) -> Term {
    let keys = lit(Value::Family(Family::set(0..d as i64)));
    let rest = lit(Value::Family(Family::set(1..d as i64)));
    fix_defined(keys, |this, k| {
        let sum = fold(
            fam_with(rest, |j| get(this, j)),
            Term::PrimFn(zed_kernel::Prim::Add),
            Some(lit(0)),
        );
        if_(eq(k.clone(), lit(0)), sum, k)
    })
}

/// The family over `0..2d` whose entry `k < d` reads the leaf `d + k`, then the entry
/// after it: `f[k] = f[d + k] + f[k + 1]`, with `f[d - 1] = f[2d - 1]` and `f[d + k] = k`.
fn reverse_chain(d: usize) -> Term {
    let n = d as i64;
    let keys = lit(Value::Family(Family::set(0..2 * n)));
    fix_defined(keys, |this, k| {
        let leaf = get(this.clone(), add(k.clone(), lit(n)));
        let next = get(this, add(k.clone(), lit(1)));
        if_(
            lt(k.clone(), lit(n - 1)),
            add(leaf.clone(), next),
            if_(lt(k.clone(), lit(n)), leaf, sub(k, lit(n))),
        )
    })
}

/// `Σ_{j=k}^{d-1} j`, the entry `k < d` of [`reverse_chain`].
fn tail_sum(d: usize, k: usize) -> i64 {
    ((k + d - 1) * (d - k) / 2) as i64
}

#[test]
fn an_entry_reading_many_undefined_entries_scales_under_demand() {
    // Each read of an undefined entry stopped the attempt, and the entry was tried again from
    // the start once the entry read was defined: entry 0 of `fan_in(d)` was tried `d` times
    // and read `d²/2` entries. Now the entry read is evaluated where it is read.
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            scaling::check("pull, one entry reading every other, by keys", 1000, |d| {
                let v = run(&fan_in(d), Schedule::Pull);
                let sum = (d * (d - 1) / 2) as i64;
                assert_eq!(
                    v.as_family().unwrap().get(&Value::Int(0)),
                    Some(&Value::Int(sum))
                );
            });
            scaling::check(
                "pull, entries reading the ones after them, by keys",
                1000,
                |d| {
                    let v = run(&reverse_chain(d), Schedule::Pull);
                    let f = v.as_family().unwrap();
                    assert_eq!(f.get(&Value::Int(0)), Some(&Value::Int(tail_sum(d, 0))));
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// The address and value of every fact of a run of `t` under `schedule`, sorted.
fn facts(t: &Term, schedule: Schedule) -> (Value, Vec<String>) {
    let mut ev = Evaluator::new(World::new())
        .with_schedule(schedule)
        .with_provenance(vec![]);
    let v = ev.run(t).unwrap();
    let p = ev.provenance().unwrap();
    let mut out: Vec<String> = p
        .facts()
        .iter()
        .map(|f| format!("{:?} {:?}", f.address, f.value))
        .collect();
    out.sort();
    (v, out)
}

#[test]
fn a_demanded_entry_has_the_facts_it_has_in_rounds() {
    // An entry demanded where it is read records its facts at its own keypath, not inside the
    // entry reading it. A chain longer than the depth of nested demands falls back to the
    // stack of demands, and an attempt stopped there drops the entries it demanded with its
    // facts, so each entry is still one set of facts.
    for d in [5, 40, zed_kernel::eval::MAX_DEPTH + 500] {
        let t = reverse_chain(d);
        let (v, pull) = facts(&t, Schedule::Pull);
        let (w, rounds) = facts(&t, Schedule::Rounds);
        assert_eq!(v, w, "d = {d}");
        let f = v.as_family().unwrap();
        for k in [0, d / 2, d - 1] {
            assert_eq!(
                f.get(&Value::Int(k as i64)),
                Some(&Value::Int(tail_sum(d, k)))
            );
        }
        assert!(pull == rounds, "d = {d}: the facts differ");
        assert_eq!(run(&t, Schedule::Pull), v, "d = {d}, untraced");
    }
}

/// The ascent from `{}` whose step is the key `count(x)` alone, joined to `x`, until `x`
/// has `n` keys.
fn ascent(n: usize) -> Term {
    let step = func(|[x]| {
        let c = count(x.clone());
        let one = reindex(
            lit(Value::Family(Family::set([0]))),
            func(|[_, _]| c.clone()),
            func(|[_, _]| lit(Value::Bool(true))),
        );
        if_(
            lt(c.clone(), lit(n as i64)),
            one,
            lit(Value::Family(Family::default())),
        )
    });
    fix_lattice(
        lit(Value::Family(Family::default())),
        step,
        Term::PrimFn(zed_kernel::Prim::Union),
    )
}

#[test]
fn a_lattice_ascent_by_one_key_a_round_scales() {
    // The test for the fixpoint compared the iterate with the one before in the total order
    // of values, reading both in full each round: `n` rounds took `O(n²)` steps (ratio 40 to
    // 44). Families are now equal by their maps, which differ at once in size.
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            scaling::check(
                "a lattice ascent adding a key a round, by keys",
                1000,
                |n| {
                    let v = run(&ascent(n), Schedule::Rounds);
                    assert_eq!(v.as_family().unwrap().len(), n);
                },
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// `"ab…"`, the `n` letters of the sequence `0..n -> letter` joined by a `foldl` of `++`.
fn joined(n: usize) -> Term {
    let letters = Family::from_leaves((0..n as i64).map(|i| {
        (
            vec![Value::Int(i)],
            Value::str(["a", "b", "c"][i as usize % 3]),
        )
    }))
    .unwrap();
    foldl(
        lit(Value::Family(letters)),
        lit(Value::str("")),
        Term::PrimFn(zed_kernel::Prim::Concat),
    )
}

#[test]
fn a_string_joined_by_a_fold_scales() {
    // `++` copied both strings, and a `foldl` keeps every accumulator, so joining `n` pieces
    // took `O(n²)` time and memory (8,000 against 64,000 pieces: ratio 26.5). A join is now
    // the node of its two parts, written out once when it is read as text.
    std::thread::Builder::new()
        .stack_size(1 << 28)
        .spawn(|| {
            scaling::check("a foldl of ++, by pieces", 8000, |n| {
                let Value::Str(s) = run(&joined(n), Schedule::Rounds) else {
                    panic!("not a string")
                };
                assert_eq!(s.len(), n);
                assert!(s.starts_with("abcab"));
            });
        })
        .unwrap()
        .join()
        .unwrap();
}
