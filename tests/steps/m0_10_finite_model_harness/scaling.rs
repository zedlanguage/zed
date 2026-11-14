//! The definedness `fix` at the rule of low complexity (DESIGN.md Part G). Each attempt at an
//! entry reads the family defined so far; copying the domain and that family into every
//! attempt made a `fix` over `D` keys cost `O(D²)` even when each entry is tried at most twice.
//! An entry postponed on an undefined key waits on it, so a chain, such as the accumulators of
//! a `foldl`, costs `D` attempts under every schedule rather than `D²/2` in rounds.
//!
//! The benchmarks of these programs are in `bench.rs`, run by `tools/run_tests.sh --bench`;
//! here each program they time runs at small sizes through the same checks
//! (TEST-bench-move-rest).

use zed_kernel::term::build::if_;
use zed_kernel::term::build::lit;
use zed_kernel::{Evaluator, Family, KernelError, Schedule, Term, Value, World};
use zed_tests::kernel::*;

/// The family `k -> k` over `0..d`, each entry above 0 reading entry 0 (`star`) or the entry
/// before it (`chain`).
pub(super) fn counts(d: usize, chain: bool) -> Term {
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

pub(super) fn run(t: &Term, schedule: Schedule) -> Value {
    Evaluator::new(World::new())
        .with_schedule(schedule)
        .run(t)
        .unwrap()
}

/// The family `k -> k` over `0..d`, the value of [`counts`] under every schedule.
fn count_family(d: usize) -> Value {
    Value::Family(
        Family::from_leaves((0..d as i64).map(|k| (vec![Value::Int(k)], Value::Int(k)))).unwrap(),
    )
}

#[test]
fn every_schedule_defines_the_counts() {
    for chain in [false, true] {
        for schedule in [Schedule::Rounds, Schedule::Pull, Schedule::Chaotic(3)] {
            assert_eq!(
                run(&counts(50, chain), schedule),
                count_family(50),
                "{schedule:?}, chain {chain}"
            );
        }
    }
}

/// The counts at small sizes under each schedule the benchmark `bench::the_definedness_fix_scales`
/// times, `Chaotic(7)` among them.
#[test]
fn the_benchmarked_schedules_define_the_counts_at_small_sizes() {
    for chain in [false, true] {
        for schedule in [Schedule::Rounds, Schedule::Chaotic(7), Schedule::Pull] {
            for d in [1, 2, 9] {
                assert_eq!(
                    run(&counts(d, chain), schedule),
                    count_family(d),
                    "{schedule:?}, chain {chain}, d = {d}"
                );
            }
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
pub(super) fn fan_in(d: usize) -> Term {
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
pub(super) fn reverse_chain(d: usize) -> Term {
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
pub(super) fn tail_sum(d: usize, k: usize) -> i64 {
    ((k + d - 1) * (d - k) / 2) as i64
}

/// Under demand, entry 0 of [`fan_in`]`(d)` sums the entries `1..d`.
pub(super) fn fan_in_sums(d: usize) {
    let v = run(&fan_in(d), Schedule::Pull);
    let sum = (d * (d - 1) / 2) as i64;
    assert_eq!(
        v.as_family().unwrap().get(&Value::Int(0)),
        Some(&Value::Int(sum))
    );
}

/// Under demand, entry 0 of [`reverse_chain`]`(d)` is [`tail_sum`]`(d, 0)`.
pub(super) fn reverse_chain_sums(d: usize) {
    let v = run(&reverse_chain(d), Schedule::Pull);
    let f = v.as_family().unwrap();
    assert_eq!(f.get(&Value::Int(0)), Some(&Value::Int(tail_sum(d, 0))));
}

/// One entry reading every other, and entries reading the ones after them, give their sums
/// under demand at small sizes; their time is held in
/// `bench::an_entry_reading_many_undefined_entries_scales_under_demand`.
#[test]
fn entries_reading_undefined_entries_give_their_sums_at_small_sizes() {
    for d in [1, 2, 9] {
        fan_in_sums(d);
        reverse_chain_sums(d);
    }
}

/// The chain of [`counts`] in reverse with its last entry reading the one before it, so that
/// every demand begun at entry 0 nests down to a cycle of two.
pub(super) fn chain_to_a_cycle(d: usize) -> Term {
    let keys = lit(Value::Family(Family::set(0..d as i64)));
    fix_defined(keys, |this, k| {
        let last = eq(k.clone(), lit(d as i64 - 1));
        let read = if_(last, sub(k.clone(), lit(1)), add(k, lit(1)));
        get(this, read)
    })
}

/// Under demand, `chain`, a [`chain_to_a_cycle`] of `d` entries, stalls on all `d`.
pub(super) fn stalls_on_every_entry(chain: &Term, d: usize) {
    let out = Evaluator::new(World::new())
        .with_schedule(Schedule::Pull)
        .run(chain);
    let Err(KernelError::Stalled { keys }) = out else {
        panic!("{out:?}")
    };
    assert_eq!(keys.len(), d);
}

/// A chain ending in a cycle stalls on every entry at small sizes (2, the cycle alone, and up);
/// its time is held in `bench::a_chain_ending_in_a_cycle_stalls_in_linear_time_under_demand`.
#[test]
fn a_chain_ending_in_a_cycle_stalls_on_every_entry_at_small_sizes() {
    for d in [2, 3, 9] {
        stalls_on_every_entry(&chain_to_a_cycle(d), d);
    }
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
    // entry reading it, at any depth of nested demands, so each entry is one set of facts.
    for d in [5, 40, zed_kernel::eval::MIN_NESTED_CALLS + 500] {
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
pub(super) fn ascent(n: usize) -> Term {
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

/// The ascent of [`ascent`]`(n)` ends with `n` keys.
pub(super) fn ascent_has_its_keys(n: usize) {
    let v = run(&ascent(n), Schedule::Rounds);
    assert_eq!(v.as_family().unwrap().len(), n);
}

/// A lattice ascent adding a key a round ends with its keys at small sizes; its time is held in
/// `bench::a_lattice_ascent_by_one_key_a_round_scales`.
#[test]
fn a_lattice_ascent_by_one_key_a_round_ends_at_small_sizes() {
    for n in [1, 2, 9] {
        ascent_has_its_keys(n);
    }
}

/// `"ab…"`, the `n` letters of the sequence `0..n -> letter` joined by a `foldl` of `++`.
pub(super) fn joined(n: usize) -> Term {
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

/// `"abcab…"`, the letters [`joined`] gives for `n` pieces, built by `push_str` and not by the
/// code under test.
pub(super) fn letters(n: usize) -> String {
    let mut want = String::new();
    for i in 0..n {
        want.push_str(["a", "b", "c"][i % 3]);
    }
    want
}

/// [`joined`]`(n)` is a string of `n` letters, the first `n` of `want`.
pub(super) fn joins_its_pieces(n: usize, want: &str) {
    let Value::Str(s) = run(&joined(n), Schedule::Rounds) else {
        panic!("not a string")
    };
    assert_eq!(s.len(), n);
    assert_eq!(s.flat(), &want[..n]);
}

/// A string joined by a `foldl` of `++` reads as its pieces at small sizes; its time is held in
/// `bench::a_string_joined_by_a_fold_scales`.
#[test]
fn a_string_joined_by_a_fold_reads_as_its_pieces_at_small_sizes() {
    let want = letters(9);
    for n in [1, 2, 9] {
        joins_its_pieces(n, &want);
    }
}
