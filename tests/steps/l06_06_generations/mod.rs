//! Step L6.6: the kernel `gen` runs a loop's guards, frames and final values.
//!
//! DESIGN sec:kernel writes a loop as `gen(init, step, guard)`, "the guard from `while`,
//! `until` and `break`", and sec:generations ("Guard timing, in full", "Frames and their
//! fields") fixes what a run gives: `while` runs first in its step and makes no frame when
//! false, `until` runs last on the complete frame, frame `t` holds the values step `t` reads
//! (`x[t-1]`) and the step-locals, and the update of the last frame is computed only where
//! something reads it. Each test here builds the kernel term a loop of DESIGN step L6.6a
//! elaborates to and checks those values. The surface loops are elaborated at step L6.3, which
//! runs the same programs from source.
//!
//! The encoding, the same for every loop, uses `gen`'s guard before each step
//! ([`GuardPos::Before`]) and no change to the term:
//!
//! - A kernel frame is a tuple whose field 0 is the step index `t`. The kernel's generation 0
//!   is a frame before the first step, index -1, holding the sentinel values; the loop's frames
//!   are the kernel's generations from 1, keyed from 0 ([`frames`]).
//! - The step reads the frame before, computes the values step `t` reads (the sentinels at
//!   `t = 0`, otherwise the update of the frame before), then the step-locals.
//! - The guard reads the frame just made: it is the `until` test on that frame (true at index
//!   -1, where no step has run) and the `while` test of the step after, at index `t + 1`.
//!   Both are tests between one committed frame and the next step, so one guard holds both,
//!   and a `while` that fails makes no frame.
//! - An update that a guard reads is a field of the frame, computed in its step; any other
//!   update is computed in the step after, and for the last frame only where the loop's value
//!   is read ([`last`]), so no step computes an update nothing reads.

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use zed_kernel::term::build::{app, if_, let_, lit, prim, var};
use zed_kernel::{Evaluator, Family, GuardPos, Lookup, Prim, Term, Value, World, eval};
use zed_tests::kernel::*;

/// `gen(pre, step, guard)`, the guard tested on each frame before the step after it.
fn generations(pre: Term, step: Term, guard: Term) -> Term {
    Term::Gen {
        init: rc(pre),
        step: rc(step),
        guard: rc(guard),
        pos: GuardPos::Before,
    }
}

/// The loop's frames: the kernel's generations of `g` after the one before the first step,
/// keyed from 0.
fn frames(g: Term) -> Term {
    let steps = discard_with(g, |p, _| prim(Prim::Gt, vec![key(p, 0), lit(0)]));
    reindex(
        steps,
        func(|[p, _]| sub(key(p, 0), lit(1))),
        func(|[_, v]| v),
    )
}

/// Field `i` of each of the loop's frames in `g`.
fn column(g: Term, i: i64) -> Term {
    map(frames(g), |f| nth(f, i))
}

/// The kernel's last generation of `g`: the loop's last frame, or the frame before the first
/// step when the loop ran none.
fn last(g: Term) -> Term {
    get(g.clone(), sub(count(g), lit(1)))
}

/// `::len`: the number of the loop's frames in `g`.
fn len(g: Term) -> Term {
    sub(count(g), lit(1))
}

/// `a || b`.
fn or(a: Term, b: Term) -> Term {
    not(and(not(a), not(b)))
}

/// True at the frame before the first step.
fn before_first(k: Term) -> Term {
    eq(nth(k, 0), lit(-1))
}

/// The loop of sec:tour_loops in one dimension, `pos.x` and `vel.x` as `pos` and `vel`, with
/// `dt = 1` and `a` always 1:
/// `sim = loop t { [while t < max_steps;] initial pos = p0; initial vel = v0; speed = vel;
/// pos' = pos + vel * dt; vel' = vel + a(pos) * dt; until pos' > bound; }`, run on `g`,
/// the gen bound to the result of `body`. Frame: `(t, pos, vel, pos', vel', speed)`; the
/// updates are fields because `until` reads `pos'`.
fn sim(p0: i64, v0: i64, bound: i64, max_steps: Option<i64>, body: Term) -> Term {
    let (dt, a) = (lit(1), lit(1));
    let step = func(|[k]| {
        let (pos, vel) = (nth(k.clone(), 3), nth(k.clone(), 4));
        prim(
            Prim::Tuple,
            vec![
                add(nth(k, 0), lit(1)),
                pos.clone(),
                vel.clone(),
                add(pos, mul(vel.clone(), dt.clone())),
                add(vel.clone(), mul(a, dt)),
                vel,
            ],
        )
    });
    let guard = func(|[k]| {
        let until = not(prim(Prim::Gt, vec![nth(k.clone(), 3), lit(bound)]));
        let go = or(before_first(k.clone()), until);
        match max_steps {
            Some(m) => and(go, lt(add(nth(k, 0), lit(1)), lit(m))),
            None => go,
        }
    });
    let pre = prim(
        Prim::Tuple,
        vec![lit(-1), lit(0), lit(0), lit(p0), lit(v0), lit(0)],
    );
    let_("g", generations(pre, step, guard), body)
}

fn g() -> Term {
    var("g")
}

#[test]
fn an_open_ended_loop_runs_until_its_guard_and_its_value_is_the_last_update() {
    // `history = sim::frames` (field `pos`), `sim.pos`, `sim::len`, `sim::frames[2].speed`,
    // `sim.speed`, and `sim::frames[3].pos`, the update step 2 made.
    let reads = prim(
        Prim::Tuple,
        vec![
            column(g(), 1),
            nth(last(g()), 3),
            len(g()),
            nth(get(frames(g()), lit(2)), 5),
            nth(last(g()), 5),
            nth(get(frames(g()), lit(3)), 1),
        ],
    );
    let out = eval(&sim(0, 1, 20, None, reads)).unwrap();
    assert_eq!(
        out.to_string(),
        "({0 -> 0, 1 -> 1, 2 -> 3, 3 -> 6, 4 -> 10, 5 -> 15}, 21, 6, 3, 6, 6)"
    );
}

#[test]
fn a_while_before_and_an_until_after_end_the_same_loop() {
    // DESIGN step L6.6's run: `bound = 2`, `max_steps = 10` gives two frames, `pos` 0 and 1,
    // ended by `until` after the frame of step 1; `max_steps = 1` gives one, ended by `while`
    // before step 1, which makes no frame. With no `while`, `final = sim.pos` is 3 and
    // `steps = sim::len` 2.
    let reads = || {
        prim(
            Prim::Tuple,
            vec![column(g(), 1), len(g()), nth(last(g()), 3)],
        )
    };
    let run = |max_steps| eval(&sim(0, 1, 2, max_steps, reads())).unwrap().to_string();
    // A family whose every value is its key prints as a set: `{0, 1}` is `{0 -> 0, 1 -> 1}`.
    assert_eq!(run(Some(10)), "({0, 1}, 2, 3)");
    assert_eq!(run(Some(1)), "({0}, 1, 1)");
    assert_eq!(run(None), "({0, 1}, 2, 3)");
}

/// `r = loop t { while t < c; initial x = 0; y = x * 2; x' = x + 1; }`, run on `g`. Frame:
/// `(t, x, y)`; no guard reads `x'`, so the update is computed in the step after, and for the
/// last frame by `r.x` alone.
fn doubles(c: i64, body: Term) -> Term {
    let step = func(|[k]| {
        let x = if_(
            before_first(k.clone()),
            lit(0),
            add(nth(k.clone(), 1), lit(1)),
        );
        let_(
            "x",
            x,
            prim(
                Prim::Tuple,
                vec![add(nth(k, 0), lit(1)), var("x"), mul(var("x"), lit(2))],
            ),
        )
    });
    let guard = func(|[k]| lt(add(nth(k, 0), lit(1)), lit(c)));
    let pre = prim(Prim::Tuple, vec![lit(-1), lit(0), lit(0)]);
    let_("g", generations(pre, step, guard), body)
}

/// `r.x`: the sentinel with zero steps, otherwise the update of the last frame.
fn final_x(g: Term) -> Term {
    let_(
        "l",
        last(g),
        if_(
            before_first(var("l")),
            lit(0),
            add(nth(var("l"), 1), lit(1)),
        ),
    )
}

/// `r.y`: the last frame's `y`, `#outOfBounds` with zero steps.
fn final_y(g: Term) -> Term {
    let_(
        "l",
        last(g),
        if_(
            before_first(var("l")),
            atom("outOfBounds"),
            nth(var("l"), 2),
        ),
    )
}

#[test]
fn a_step_local_on_the_loop_is_the_last_frames_and_zero_steps_give_the_sentinels() {
    let reads = || {
        prim(
            Prim::Tuple,
            vec![column(g(), 1), column(g(), 2), final_x(g()), final_y(g())],
        )
    };
    assert_eq!(
        eval(&doubles(3, reads())).unwrap().to_string(),
        "({0, 1, 2}, {0 -> 0, 1 -> 2, 2 -> 4}, 3, 4)"
    );
    assert_eq!(
        eval(&doubles(0, reads())).unwrap().to_string(),
        "({}, {}, 0, #outOfBounds)"
    );
}

#[test]
fn a_loop_of_only_until_runs_at_least_one_step() {
    // `loop { initial x = 0; x' = x + 1; until x' >= 3; }`. Frame: `(t, x, x')`.
    let step = func(|[k]| {
        let x = nth(k.clone(), 2);
        prim(
            Prim::Tuple,
            vec![add(nth(k, 0), lit(1)), x.clone(), add(x, lit(1))],
        )
    });
    let guard = func(|[k]| or(before_first(k.clone()), lt(nth(k, 2), lit(3))));
    let pre = prim(Prim::Tuple, vec![lit(-1), lit(0), lit(0)]);
    let reads = prim(Prim::Tuple, vec![column(g(), 1), nth(last(g()), 2)]);
    let out = eval(&let_("g", generations(pre, step, guard), reads)).unwrap();
    assert_eq!(out.to_string(), "({0, 1, 2}, 3)");
    // A guard that ends the loop at once still leaves the first step's frame.
    let at_once = generations(
        prim(Prim::Tuple, vec![lit(-1)]),
        func(|[k]| prim(Prim::Tuple, vec![add(nth(k, 0), lit(1))])),
        func(|[k]| before_first(k)),
    );
    let out = eval(&let_("g", at_once, len(g()))).unwrap();
    assert_eq!(out, Value::Int(1));
}

/// A called port that gives its argument plus one and counts its calls.
#[derive(Debug, Default)]
struct Probe(AtomicUsize);

impl Lookup for Probe {
    fn get(&self, key: &Value) -> Result<Value, String> {
        self.0.fetch_add(1, Ordering::SeqCst);
        match key {
            Value::Tuple(xs) => match &xs[..] {
                [Value::Int(x)] => Ok(Value::Int(x + 1)),
                _ => Err(format!("probe called with {key}")),
            },
            _ => Err(format!("probe called with {key}")),
        }
    }

    fn calls(&self) -> bool {
        true
    }
}

#[test]
fn the_last_update_is_computed_only_where_the_loops_value_is_read() {
    // `r = loop t { while t < 3; initial x = 1; x' = probe(x); }`: three frames, `x` 1, 2, 3.
    // Steps 1 and 2 call `probe` for the values they read; the update of step 2 is computed
    // only for `r.x`.
    let step = func(|[k]| {
        let x = if_(
            before_first(k.clone()),
            lit(1),
            app(Term::Read("probe".into()), vec![nth(k.clone(), 1)]),
        );
        prim(Prim::Tuple, vec![add(nth(k, 0), lit(1)), x])
    });
    let guard = func(|[k]| lt(add(nth(k, 0), lit(1)), lit(3)));
    let pre = prim(Prim::Tuple, vec![lit(-1), lit(0)]);
    let r_x = app(Term::Read("probe".into()), vec![nth(last(g()), 1)]);
    let run = |reads: Term| {
        let probe = Arc::new(Probe::default());
        let mut ev = Evaluator::new(World::new().source("probe", probe.clone()));
        let loop_ = let_(
            "g",
            generations(pre.clone(), step.clone(), guard.clone()),
            reads,
        );
        let out = ev.run(&loop_).unwrap();
        (out.to_string(), probe.0.load(Ordering::SeqCst))
    };
    assert_eq!(run(column(g(), 1)), ("{0 -> 1, 1 -> 2, 2 -> 3}".into(), 2));
    assert_eq!(run(r_x), ("4".into(), 3));
}

#[test]
fn the_step_that_reaches_a_break_makes_the_last_frame() {
    // `loop t { while t < 4; if xs[t] < 0 { break; }; y = xs[t] * 2; }` with
    // `xs = [3, 5, -1, 4]`. Frame: `(t, broke, y)`. Step 2 reaches the `break`: it has a frame,
    // the binding after the `break` is `#skippedByBreak` there (DESIGN step L6.6b), and the
    // guard ends the loop after it, before the `while` of step 3.
    let xs = lit(Value::Family(Family::of(
        [3, 5, -1, 4]
            .into_iter()
            .enumerate()
            .map(|(i, x)| (Value::Int(i as i64), Value::Int(x))),
    )));
    let step = func(|[k]| {
        let t = add(nth(k, 0), lit(1));
        let_(
            "v",
            get(xs, t.clone()),
            let_(
                "b",
                lt(var("v"), lit(0)),
                prim(
                    Prim::Tuple,
                    vec![
                        t,
                        var("b"),
                        if_(var("b"), atom("skippedByBreak"), mul(var("v"), lit(2))),
                    ],
                ),
            ),
        )
    });
    let guard = func(|[k]| and(not(nth(k.clone(), 1)), lt(add(nth(k, 0), lit(1)), lit(4))));
    let pre = prim(Prim::Tuple, vec![lit(-1), lit(false), lit(0)]);
    let reads = prim(Prim::Tuple, vec![column(g(), 2), len(g())]);
    let out = eval(&let_("g", generations(pre, step, guard), reads)).unwrap();
    assert_eq!(
        out.to_string(),
        "({0 -> 6, 1 -> 10, 2 -> #skippedByBreak}, 3)"
    );
}
