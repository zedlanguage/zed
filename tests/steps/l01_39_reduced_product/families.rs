//! The families of tests that the cross-review LAZY-hub-xr built for the reduced product
//! (six rounds, closed with no change to `product.rs`), kept as tests. Each family is a scope
//! of integer names and a list of tests assumed one after another, at a size `k`, and some end
//! with a test whose two arms are joined.
//!
//! Each family is checked three ways:
//! - against an oracle that lists the integer points of a window of the names the tests
//!   mention: every value a point gives a name must be in the name's product (soundness), and
//!   both the scope's facts and the oracle's are pinned, so that a fact the oracle finds and
//!   the scope does not is written down beside the case that misses it;
//! - by its growth in `k`, held to the rule of low complexity at `n` and `8n`
//!   (`scaling::check`); a family on which main grows faster than linearly is ignored with
//!   the item that would fix it;
//! - and the 1152 records of the review's random audit, each checked for soundness, with the
//!   three records that no candidate of the review recovered pinned (all three found since,
//!   LAZY-hub-unsolved).

use std::collections::BTreeMap;
use std::sync::Arc;

use zed_kernel::{Prim, Term, Value};
use zed_tests::scaling;
use zedc::store::cell::Premises;
use zedc::store::interval::{End, IntervalSet};
use zedc::store::product::{Product, Scope};

use super::ints;

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

fn int(n: i64) -> Term {
    Term::Lit(Value::Int(n))
}

fn ge(a: Term, b: Term) -> Term {
    prim(Prim::Ge, a, b)
}

fn le(a: Term, b: Term) -> Term {
    prim(Prim::Le, a, b)
}

fn eq(a: Term, b: Term) -> Term {
    prim(Prim::Eq, a, b)
}

fn or(a: Term, b: Term) -> Term {
    prim(Prim::Or, a, b)
}

fn and(a: Term, b: Term) -> Term {
    prim(Prim::And, a, b)
}

fn add(a: Term, b: Term) -> Term {
    prim(Prim::Add, a, b)
}

fn sub(a: Term, b: Term) -> Term {
    prim(Prim::Sub, a, b)
}

/// `j * x`, written as a product even for `j` = 1.
fn times(j: i64, x: &str) -> Term {
    prim(Prim::Mul, int(j), var(x))
}

/// `x + j * y >= 1 || x - j * y >= 1`: none of these implies another for distinct `j`.
fn split_on_y(j: i64) -> Term {
    or(
        ge(add(var("x"), times(j, "y")), int(1)),
        ge(sub(var("x"), times(j, "y")), int(1)),
    )
}

/// `x - y <= -j || x + y <= -j`, that is `x <= |y| - j`.
fn below_abs_y(j: i64) -> Term {
    or(
        le(sub(var("x"), var("y")), int(-j)),
        le(add(var("x"), var("y")), int(-j)),
    )
}

/// The star `a >= x + y`: `a` is a hub that no later test mentions.
fn star() -> Term {
    ge(var("a"), add(var("x"), var("y")))
}

/// `x >= c || y <= d`: one step of a staircase.
fn step(c: i64, d: i64) -> Term {
    or(ge(var("x"), int(c)), le(var("y"), int(d)))
}

/// `-b <= n <= b` for each of `names`.
fn boxed(names: &[&str], b: i64) -> Vec<Term> {
    names
        .iter()
        .flat_map(|n| [ge(var(n), int(-b)), le(var(n), int(b))])
        .collect()
}

/// The names `z0` to `z(k-1)`.
fn zs(k: usize) -> Vec<String> {
    (0..k).map(|j| format!("z{j}")).collect()
}

/// `z0 + z1 + ... + z(k-1)`.
fn sum_of_zs(k: usize) -> Term {
    (1..k).fold(var("z0"), |s, j| add(s, var(&format!("z{j}"))))
}

/// A scope at one size: its names, the tests assumed in order, a test whose two arms are joined
/// at the end, and the window of the names the tests mention that the oracle lists.
struct Family {
    names: Vec<Arc<str>>,
    tests: Vec<Term>,
    join: Option<Term>,
    window: Vec<(String, i64, i64)>,
}

/// Every name in `names` within `-r..=r`.
fn around(names: &[&str], r: i64) -> Vec<(String, i64, i64)> {
    names.iter().map(|n| (n.to_string(), -r, r)).collect()
}

/// The two-arm hole tests of `hole_end*`: `x <= 1`, or `y == 2` and `x <= 3`, or `y == 5`
/// and `4 <= x <= 6`, or `y >= top` and `x >= 7`.
fn hole_test(top: i64) -> Term {
    or(
        or(
            le(var("x"), int(1)),
            and(
                and(ge(var("y"), int(2)), le(var("y"), int(2))),
                le(var("x"), int(3)),
            ),
        ),
        or(
            and(
                and(ge(var("y"), int(5)), le(var("y"), int(5))),
                and(ge(var("x"), int(4)), le(var("x"), int(6))),
            ),
            and(ge(var("y"), int(top)), ge(var("x"), int(7))),
        ),
    )
}

/// Family `name` at size `k` (ignored by the families of one size).
fn family(name: &str, k: usize) -> Family {
    let ki = k as i64;
    let mut names = vec!["a".to_string(), "x".to_string(), "y".to_string()];
    let mut tests = Vec::new();
    let mut join = None;
    let xy = ["x", "y"];
    let window = match name {
        // The star, then `k` splits on its hubs, of which none implies another.
        "star" => {
            tests.push(star());
            tests.extend((1..=ki).map(split_on_y));
            around(&xy, 20)
        }
        // The star, then each split with a third arm `x >= 1`.
        "star_extra" => {
            tests.push(star());
            tests.extend((1..=ki).map(|j| or(split_on_y(j), ge(var("x"), int(1)))));
            around(&xy, 20)
        }
        // The star, then each split with a third arm `x + j * a >= 1`, which reads the star's
        // own hub.
        "star_mixed" => {
            tests.push(star());
            tests.extend(
                (1..=ki).map(|j| or(split_on_y(j), ge(add(var("x"), times(j, "a")), int(1)))),
            );
            around(&["a", "x", "y"], 12)
        }
        // The splits alone, with no star.
        "hubs" => {
            tests.extend((1..=ki).map(split_on_y));
            around(&xy, 20)
        }
        // A box, the star, then for each `j` the split `j` and `x <= |y| - j`, which cuts the
        // top of `x`.
        "chain" => {
            tests.extend(boxed(&xy, 4 * ki));
            tests.push(star());
            for j in 1..=ki {
                tests.push(split_on_y(j));
                tests.push(below_abs_y(j));
            }
            around(&xy, 4 * ki + 1)
        }
        // A box, the star, then the splits: after the first no test moves an interval.
        "boxstar" => {
            tests.extend(boxed(&xy, 4 * ki));
            tests.push(star());
            tests.extend((1..=ki).map(split_on_y));
            around(&xy, 4 * ki + 1)
        }
        // A box, the star, then only the cuts `x <= |y| - j`.
        "cuts" => {
            tests.extend(boxed(&xy, 4 * ki));
            tests.push(star());
            tests.extend((1..=ki).map(below_abs_y));
            around(&xy, 4 * ki + 1)
        }
        // The star and the splits, then the two arms of `x - y >= 0` joined.
        "starjoin" => {
            tests.push(star());
            tests.extend((1..=ki).map(split_on_y));
            join = Some(ge(sub(var("x"), var("y")), int(0)));
            around(&xy, 20)
        }
        // The star, then each split followed by a plain constraint `x + j * y >= -1000`.
        "persist" => {
            tests.push(star());
            for j in 1..=ki {
                tests.push(split_on_y(j));
                tests.push(ge(add(var("x"), times(j, "y")), int(-1000)));
            }
            around(&xy, 2100)
        }
        // `k` steps `x >= i || y <= -1000 + i`, then `k` tests `x + y <= -j || x + 2 * y <=
        // -5000 - j`; `coordkk_y` starts with `y <= 0`.
        "coordkk" | "coordkk_y" => {
            if name == "coordkk_y" {
                tests.push(le(var("y"), int(0)));
            }
            tests.extend((1..=ki).map(|i| step(i, -1000 + i)));
            tests.extend((1..=ki).map(|j| {
                or(
                    le(add(var("x"), var("y")), int(-j)),
                    le(add(var("x"), times(2, "y")), int(-5000 - j)),
                )
            }));
            vec![("x".into(), -60, 60), ("y".into(), -6100, 60)]
        }
        // One step `x >= 0 || y <= -10k`, then `k` splits (shifted by 10k in
        // `coordmix_shift`), then `k` tests `x + y <= -j || x + 2 * y <= -50k - j`;
        // `coordmix_floor` puts `y >= -100k` before the tests.
        "coordmix" | "coordmix_shift" | "coordmix_floor" => {
            tests.push(step(0, -10 * ki));
            tests.extend((1..=ki).map(|j| {
                if name == "coordmix_shift" {
                    or(
                        ge(add(var("x"), times(j + 2, "y")), int(10 * ki)),
                        ge(sub(var("x"), times(j + 2, "y")), int(10 * ki)),
                    )
                } else {
                    split_on_y(j + 2)
                }
            }));
            if name == "coordmix_floor" {
                tests.push(ge(var("y"), int(-100 * ki)));
            }
            tests.extend((1..=ki).map(|j| {
                or(
                    le(add(var("x"), var("y")), int(-j)),
                    le(add(var("x"), times(2, "y")), int(-50 * ki - j)),
                )
            }));
            // coordmix_floor bounds `x` below by `1 + 3y >= -300k + 1`.
            around(
                &xy,
                if name == "coordmix_floor" {
                    300 * ki + 20
                } else {
                    210 * ki
                },
            )
        }
        // coordmix with tests whose slopes `q = k + j + 3` differ from every split's.
        "coordmix_unmatched" => {
            tests.push(step(0, -10 * ki));
            tests.extend((1..=ki).map(|j| split_on_y(j + 2)));
            tests.extend((1..=ki).map(|j| {
                let q = ki + j + 3;
                or(
                    le(add(var("x"), times(q, "y")), int(-j * q)),
                    le(add(var("x"), times(2 * q, "y")), int(-(50 * ki + j) * q)),
                )
            }));
            around(&xy, 60 * ki * (2 * ki + 3))
        }
        // coordmix with tests of slopes `j` and `2j`.
        "coordmix_slopes" => {
            tests.push(step(0, -10 * ki));
            tests.extend((1..=ki).map(|j| split_on_y(j + 2)));
            tests.extend((1..=ki).map(|j| {
                or(
                    le(add(var("x"), times(j, "y")), int(-j * j)),
                    le(add(var("x"), times(2 * j, "y")), int(-50 * ki * j - j * j)),
                )
            }));
            around(&xy, 210 * ki)
        }
        // One disjunction of two arms, each the conjunction of `k` rows on `x` and `y`:
        // `x + s * j * y >= -j * j` for `j` = 1 to `k`, `s` = 1 in one arm and -1 in the other.
        "rows_one_pair" => {
            let arm = |s: i64| {
                (2..=ki).fold(ge(add(var("x"), times(s, "y")), int(-1)), |out, j| {
                    and(out, ge(add(var("x"), times(s * j, "y")), int(-j * j)))
                })
            };
            tests.push(or(arm(1), arm(-1)));
            around(&xy, 3 * ki * ki + 10)
        }
        // One disjunction of two arms, each the conjunction of `z(j) + z(j+1) >= 0` (or with
        // `-` in the other arm) over the adjacent pairs of `z0` to `z(k-1)`.
        "wide_pairs" => {
            let z = zs(k);
            let arm = |p: Prim| {
                (0..k.saturating_sub(1))
                    .map(|j| ge(prim(p, var(&z[j]), var(&z[j + 1])), int(0)))
                    .reduce(and)
                    .unwrap_or_else(|| ge(var("z0"), int(0)))
            };
            tests.push(or(arm(Prim::Add), arm(Prim::Sub)));
            let refs: Vec<&str> = z.iter().map(String::as_str).collect();
            let w = around(&refs, 5);
            names.extend(z);
            w
        }
        // Under `x + y <= 12`, the steps `x >= 10i || y >= 17 - 10i`, each of which cuts the
        // hole `10i - 4..=10i - 1` in `x`: in order (`stair_holes`), odd `i` then even
        // (`stair_holes_mix`), or that order with `x + y <= 12` last (`stair_holes_late`).
        "stair_holes" | "stair_holes_mix" | "stair_holes_late" => {
            let sum = le(add(var("x"), var("y")), int(12));
            if name != "stair_holes_late" {
                tests.push(sum.clone());
            }
            let order: Vec<i64> = if name == "stair_holes" {
                (1..=ki).collect()
            } else {
                (1..=ki).step_by(2).chain((2..=ki).step_by(2)).collect()
            };
            tests.extend(
                order
                    .into_iter()
                    .map(|i| or(ge(var("x"), int(10 * i)), ge(var("y"), int(17 - 10 * i)))),
            );
            if name == "stair_holes_late" {
                tests.push(sum);
            }
            around(&xy, 10 * ki + 40)
        }
        // `x >= 0`, `y >= 0`, `x + y <= 1000`, then `x >= i || y >= 1000 - i`: no step
        // narrows a name.
        "stair_cover" => {
            tests.push(ge(var("x"), int(0)));
            tests.push(ge(var("y"), int(0)));
            tests.push(le(add(var("x"), var("y")), int(1000)));
            tests.extend((1..=ki).map(|i| or(ge(var("x"), int(i)), ge(var("y"), int(1000 - i)))));
            vec![("x".into(), -1, 1001), ("y".into(), -1, 1001)]
        }
        // stair_cover with no box: `x + y <= 0`, then `x >= i || y >= -i`.
        "stair_cover_free" => {
            tests.push(le(add(var("x"), var("y")), int(0)));
            tests.extend((1..=ki).map(|i| or(ge(var("x"), int(i)), ge(var("y"), int(-i)))));
            around(&xy, 4 * ki + 40)
        }
        // A sum of `k` names at least -1000, then `sum >= j || z0 <= -j` for each `j`.
        "wide" => {
            tests.push(ge(sum_of_zs(k), int(-1000)));
            for j in 1..=ki {
                tests.push(or(ge(sum_of_zs(k), int(j)), le(var("z0"), int(-j))));
            }
            let z = zs(k);
            let refs: Vec<&str> = z.iter().map(String::as_str).collect();
            let w = around(&refs, if k == 1 { 1005 } else { 5 });
            names.extend(z);
            w
        }
        // `x` in 0..=1, `y` and `z` in -1000..=1000, the star `a >= x + y + z`, then `k`
        // parts `x <= 0 || y + i * z >= c + 1 || y + i * z <= c - 1` with `c = 4 + 5i`, so that
        // the point (y, z) = (3, 5) is on no line `y + i * z = c`; on `hopon` the last `c` is
        // `3 + 5k`, whose line holds it. `hop` and `hopon` then fix (y, z) = (3, 5) by
        // `y + z == 8` and `y - z == -2`; `hopb` and `hoponb` stop before. The answer on
        // `hop` is `x` in 0..=1, and on `hopon` `x` = 0.
        "hop" | "hopon" | "hopb" | "hoponb" => {
            names.push("z".into());
            tests.push(ge(var("x"), int(0)));
            tests.push(le(var("x"), int(1)));
            for n in ["y", "z"] {
                tests.push(ge(var(n), int(-1000)));
                tests.push(le(var(n), int(1000)));
            }
            tests.push(ge(var("a"), add(add(var("x"), var("y")), var("z"))));
            for i in 1..=ki {
                let c = if name.starts_with("hopon") && i == ki {
                    3 + 5 * i
                } else {
                    4 + 5 * i
                };
                let l = || add(var("y"), times(i, "z"));
                tests.push(or(
                    le(var("x"), int(0)),
                    or(ge(l(), int(c + 1)), le(l(), int(c - 1))),
                ));
            }
            if !name.ends_with('b') {
                tests.push(eq(add(var("y"), var("z")), int(8)));
                tests.push(eq(sub(var("y"), var("z")), int(-2)));
            }
            vec![
                ("x".into(), -1, 2),
                ("y".into(), -1001, 1001),
                ("z".into(), -1001, 1001),
            ]
        }
        // A step on `x` and `y`, then a test whose first arm links them again.
        "armlink" => {
            tests.push(step(10, -9));
            tests.push(or(
                le(add(var("x"), var("y")), int(14)),
                ge(var("y"), int(100)),
            ));
            vec![("x".into(), -150, 150), ("y".into(), -150, 150)]
        }
        // armlink after `x + y <= 1000`, which links the two names outside the test.
        "armlink2" => {
            tests.push(le(add(var("x"), var("y")), int(1000)));
            tests.push(step(10, -9));
            tests.push(or(
                le(add(var("x"), var("y")), int(14)),
                ge(var("y"), int(100)),
            ));
            // `y` reaches 990, at `x` = 10.
            around(&xy, 1100)
        }
        // armlink with the link through `a`: `a - y <= 0` outside, `x + a <= 14` in the arm.
        "armlink3" => {
            tests.push(le(sub(var("a"), var("y")), int(0)));
            tests.push(step(10, -9));
            tests.push(or(
                le(add(var("x"), var("a")), int(14)),
                ge(var("y"), int(100)),
            ));
            vec![
                ("a".into(), -40, 40),
                ("x".into(), -40, 40),
                ("y".into(), -120, 120),
            ]
        }
        // A step, then a test both of whose arms link `x` and `y`.
        "coord3" => {
            tests.push(step(10, -9));
            tests.push(or(
                le(add(var("x"), var("y")), int(14)),
                le(add(var("x"), times(2, "y")), int(-100)),
            ));
            around(&xy, 150)
        }
        // A step, a test whose arms bound `x + y` from above, then a test the threshold
        // aggregate does not read, which ends the aggregate and moves no name. For `y >= 0`
        // the second test gives `x <= -1`, and then neither arm of the third holds.
        "upper_release" => {
            tests.push(step(6, 5));
            tests.push(or(
                le(add(times(2, "x"), var("y")), int(-2)),
                le(add(var("x"), times(3, "y")), int(-5)),
            ));
            tests.push(or(
                ge(add(var("x"), var("y")), int(6)),
                ge(sub(var("x"), times(2, "y")), int(1)),
            ));
            around(&xy, 40)
        }
        // Audit record 108:3 cut down: every name in -8..=8, `3a <= z + 2`, then
        // `a >= -3 || y == z - 1`, then `(a + x >= -3 || x == z) && (x >= 4 || z >= 2a)`. In
        // the case `z >= 2a` the first part gives `z >= -7`: its first arm gives `z >= -6`
        // there, its second `z >= -7` from `y >= -8`; then `x == z` gives `x >= -7`, as
        // `a + x >= -3` with `a <= 3` gives `x >= -6`. drop_ends repeats the two disjunctions
        // `k` times, the `j`-th moved by `j`.
        "drop_end" | "drop_ends" => {
            names.push("z".into());
            tests.extend(boxed_from(&["a", "x", "y", "z"], -8, 8));
            tests.push(le(times(3, "a"), add(var("z"), int(2))));
            let js = if name == "drop_end" { 0..1 } else { 0..ki };
            for j in js.clone() {
                tests.push(or(
                    ge(var("a"), int(-3 - j)),
                    eq(var("y"), sub(var("z"), int(1 + j))),
                ));
            }
            for j in js {
                tests.push(and(
                    or(
                        ge(add(var("a"), var("x")), int(-3 - j)),
                        eq(var("x"), var("z")),
                    ),
                    or(
                        ge(var("x"), int(4 + j)),
                        ge(var("z"), add(times(2, "a"), int(j))),
                    ),
                ));
            }
            around(&["a", "x", "y", "z"], 9)
        }
        // `x`, `y` in 0..=10, then `x == 0 || y == 0`, `x == 1 || y == 1`, two steps, and
        // `x + y <= 10`.
        "exit_order" => {
            tests.extend(boxed_from(&xy, 0, 10));
            tests.push(or(eq(var("x"), int(0)), eq(var("y"), int(0))));
            tests.push(or(eq(var("x"), int(1)), eq(var("y"), int(1))));
            tests.push(step(8, 1));
            tests.push(step(9, 0));
            tests.push(le(add(var("x"), var("y")), int(10)));
            vec![("x".into(), -1, 11), ("y".into(), -1, 11)]
        }
        // A box of 8, the steps at (0, 0), (2, 1), (3, 3), (4, 5), (6, 6), then `x + y <= 6`;
        // `stair_hull_vertices` leaves out (3, 3), which lies in the hull of the others.
        "stair_hull" | "stair_hull_vertices" => {
            tests.extend(boxed(&xy, 8));
            for (c, d) in [(0, 0), (2, 1), (3, 3), (4, 5), (6, 6)] {
                if name == "stair_hull_vertices" && (c, d) == (3, 3) {
                    continue;
                }
                tests.push(step(c, d));
            }
            tests.push(le(add(var("x"), var("y")), int(6)));
            around(&xy, 9)
        }
        // A step on (x, y), `y >= 5 || a <= 0`, then `x + y <= 14 || (y >= 5 && a <= 0)`.
        "m1_trans_ce" => {
            tests.push(step(10, -9));
            tests.push(or(ge(var("y"), int(5)), le(var("a"), int(0))));
            tests.push(or(
                le(add(var("x"), var("y")), int(14)),
                and(ge(var("y"), int(5)), le(var("a"), int(0))),
            ));
            around(&["a", "x", "y"], 30)
        }
        // The step `x >= 10 || y <= -9` and the part `a <= y || a <= -50` on (y, a), with
        // `x <= 5` last (side1), the part first (side2), `x <= 5 || x <= 3` in place of
        // `x <= 5` (side3), or coord3's test and then the part (side4).
        "side1" | "side2" | "side3" | "side4" => {
            let part = or(le(sub(var("a"), var("y")), int(0)), le(var("a"), int(-50)));
            if name == "side2" {
                tests.push(part.clone());
            }
            tests.push(step(10, -9));
            if name == "side1" || name == "side3" {
                tests.push(part.clone());
            }
            match name {
                "side3" => tests.push(or(le(var("x"), int(5)), le(var("x"), int(3)))),
                "side4" => {
                    tests.push(or(
                        le(add(var("x"), var("y")), int(14)),
                        le(add(var("x"), times(2, "y")), int(-100)),
                    ));
                    tests.push(part);
                }
                _ => tests.push(le(var("x"), int(5))),
            }
            vec![
                ("a".into(), -60, 60),
                ("x".into(), -120, 120),
                ("y".into(), -120, 120),
            ]
        }
        // The step, then `x - y <= 3 || x <= -100` in its block, then `x <= 5`.
        "side5" => {
            tests.push(step(10, -9));
            tests.push(or(
                le(sub(var("x"), var("y")), int(3)),
                le(var("x"), int(-100)),
            ));
            tests.push(le(var("x"), int(5)));
            around(&xy, 150)
        }
        // `x`, `y` in 0..=10 and the two hole tests (hole_end0); then `x + y <= 10 || 3x + y
        // >= 37` (hole_end1); then `x <= 8` (hole_end2). The `_pad` forms first add `k`
        // disjunctions `x + j*y >= -1000j || x - j*y >= 1000j` that the box makes redundant,
        // so the block that holds the hole has `k` more parts.
        "hole_end0" | "hole_end1" | "hole_end2" | "hole_end1_pad" | "hole_end2_pad" => {
            if name.ends_with("_pad") {
                tests.extend((1..=ki).map(|j| {
                    or(
                        ge(add(var("x"), times(j, "y")), int(-1000 * j)),
                        ge(sub(var("x"), times(j, "y")), int(1000 * j)),
                    )
                }));
            }
            let name = name.trim_end_matches("_pad");
            tests.extend(boxed_from(&xy, 0, 10));
            tests.push(hole_test(10));
            tests.push(hole_test(9));
            if name != "hole_end0" {
                tests.push(or(
                    le(add(var("x"), var("y")), int(10)),
                    ge(add(times(3, "x"), var("y")), int(37)),
                ));
            }
            if name == "hole_end2" {
                tests.push(le(var("x"), int(8)));
            }
            vec![("x".into(), -1, 11), ("y".into(), -1, 11)]
        }
        // A part that the plain constraint `x - y <= 0` gives a hole: `y` in `..=-9` or
        // `10..`. hole1s puts the star first, hole2 the split 2, hole2s both, and hole2c adds
        // `x >= -5 || x <= -7`.
        "hole1" | "hole1s" | "hole2" | "hole2s" | "hole2c" => {
            if name == "hole1s" || name == "hole2s" {
                tests.push(star());
            }
            if name.starts_with("hole2") {
                tests.push(split_on_y(2));
            }
            tests.push(step(10, -9));
            tests.push(le(sub(var("x"), var("y")), int(0)));
            if name == "hole2c" {
                tests.push(or(ge(var("x"), int(-5)), le(var("x"), int(-7))));
            }
            around(&xy, 40)
        }
        // `a`, `b` in 0..=100000, `a + b <= 150000`, `a <= 2 || b >= 8`, then `k` equalities
        // `a + b - zi == i` (hub_eqs) or `a - zi == i` (hub_alias), each with a name of its own.
        "hub_eqs" | "hub_alias" => {
            names = vec!["a".into(), "b".into()];
            names.extend((0..k).map(|i| format!("z{i}")));
            tests.extend(boxed_from(&["a", "b"], 0, 100_000));
            tests.push(le(add(var("a"), var("b")), int(150_000)));
            tests.push(or(le(var("a"), int(2)), ge(var("b"), int(8))));
            for i in 0..ki {
                let l = if name == "hub_eqs" {
                    add(var("a"), var("b"))
                } else {
                    var("a")
                };
                tests.push(eq(sub(l, var(&format!("z{i}"))), int(i)));
            }
            around(&["a", "b"], 3)
        }
        // `k` names `zi`, all at least 1 or all at most -1 (one disjunction of two arms of `k`
        // constraints each), then `z0 + z(k-1) >= 5 || x <= 0`.
        "unary_arms" => {
            let z = |i: i64| var(&format!("z{i}"));
            let all = |f: &dyn Fn(i64) -> Term| (1..ki).fold(f(0), |s, i| and(s, f(i)));
            names.extend((0..k).map(|i| format!("z{i}")));
            tests.push(or(all(&|i| ge(z(i), int(1))), all(&|i| le(z(i), int(-1)))));
            tests.push(or(ge(add(z(0), z(ki - 1)), int(5)), le(var("x"), int(0))));
            let mut window: Vec<(String, i64, i64)> =
                (0..k).map(|i| (format!("z{i}"), -6, 6)).collect();
            window.push(("x".into(), -6, 6));
            window
        }
        // `a <= 2 || b >= 8`, `a == 3 * z0`, `a == 2 * z1 + 1`, then `b - z1 <= 4 || z1 >= 20`
        // (k = 0) or `b - z1 <= 4` (k = 1). In the arm `a <= 2`, `a` is odd and a multiple of
        // 3, so `a <= -3` and `z1 <= -2`, and the last test gives `b <= 2`.
        "two_eq_case" => {
            names = vec!["a".into(), "b".into(), "z0".into(), "z1".into()];
            tests.push(or(le(var("a"), int(2)), ge(var("b"), int(8))));
            tests.push(eq(sub(var("a"), times(3, "z0")), int(0)));
            tests.push(eq(sub(var("a"), times(2, "z1")), int(1)));
            let last = le(sub(var("b"), var("z1")), int(4));
            tests.push(if k == 0 {
                or(last, ge(var("z1"), int(20)))
            } else {
                last
            });
            vec![
                ("a".into(), -6, 12),
                ("b".into(), -3, 10),
                ("z0".into(), -3, 6),
                ("z1".into(), -4, 8),
            ]
        }
        _ => panic!("no family {name}"),
    };
    Family {
        names: names.into_iter().map(Arc::from).collect(),
        tests,
        join,
        window,
    }
}

/// `lo <= n <= hi` for each of `names`.
fn boxed_from(names: &[&str], lo: i64, hi: i64) -> Vec<Term> {
    names
        .iter()
        .flat_map(|n| [ge(var(n), int(lo)), le(var(n), int(hi))])
        .collect()
}

/// The scope of `f`: each test assumed true in order, then the arms of its join joined.
fn run(f: &Family) -> Scope {
    let p = Premises::new();
    let s = f
        .tests
        .iter()
        .fold(ints(&f.names), |s, t| s.assume(t, true, &p));
    match &f.join {
        Some(j) => s.assume(j, true, &p).join(&s.assume(j, false, &p)),
        None => s,
    }
}

/// A name's facts as the tests print them: its integers, and its class when that is not every
/// integer and the integers are not one value.
fn shown(p: &Product) -> String {
    let ints = p.ints().to_string();
    let class = p.cell.congruence.element.to_string();
    let one = p.ints().only().is_some_and(|(lo, hi)| lo == hi);
    if class == "any" || one {
        ints
    } else {
        format!("{ints} {class}")
    }
}

/// The scope's facts: `bottom`, or `name=facts` for each name, in order.
fn facts(s: &Scope, names: &[Arc<str>]) -> String {
    if s.bottom {
        return "bottom".into();
    }
    names
        .iter()
        .map(|n| format!("{n}={}", shown(&s.get(n))))
        .collect::<Vec<_>>()
        .join(" ")
}

/// A linear form: `coef[i]` times the `i`th name of the oracle, plus `constant`.
#[derive(Clone)]
struct Linear {
    coef: Vec<i64>,
    constant: i64,
}

impl Linear {
    fn at(&self, point: &[i64]) -> i64 {
        self.coef.iter().zip(point).map(|(c, v)| c * v).sum::<i64>() + self.constant
    }

    fn scaled(mut self, by: i64) -> Linear {
        self.coef.iter_mut().for_each(|c| *c *= by);
        self.constant *= by;
        self
    }

    fn plus(mut self, o: &Linear) -> Linear {
        self.coef.iter_mut().zip(&o.coef).for_each(|(a, b)| *a += b);
        self.constant += o.constant;
        self
    }
}

/// A test the oracle evaluates: a linear form at least 0 or equal to 0, or the disjunction or
/// conjunction of two.
enum Cond {
    AtLeastZero(Linear),
    Zero(Linear),
    Or(Box<Cond>, Box<Cond>),
    And(Box<Cond>, Box<Cond>),
}

impl Cond {
    fn holds(&self, point: &[i64]) -> bool {
        match self {
            Cond::AtLeastZero(l) => l.at(point) >= 0,
            Cond::Zero(l) => l.at(point) == 0,
            Cond::Or(a, b) => a.holds(point) || b.holds(point),
            Cond::And(a, b) => a.holds(point) && b.holds(point),
        }
    }

    /// Whether name `i` has a coefficient other than 0 anywhere in the test.
    fn mentions(&self, i: usize) -> bool {
        match self {
            Cond::AtLeastZero(l) | Cond::Zero(l) => l.coef[i] != 0,
            Cond::Or(a, b) | Cond::And(a, b) => a.mentions(i) || b.mentions(i),
        }
    }
}

/// The linear form of `t` over `names`; the families write only sums, differences and
/// products by a literal.
fn linear(t: &Term, names: &[String]) -> Linear {
    let zero = || Linear {
        coef: vec![0; names.len()],
        constant: 0,
    };
    match t {
        Term::Lit(Value::Int(c)) => Linear {
            constant: *c,
            ..zero()
        },
        Term::Var(n) => {
            let mut l = zero();
            let i = names
                .iter()
                .position(|m| **m == **n)
                .expect("a name of the window");
            l.coef[i] = 1;
            l
        }
        Term::Prim(Prim::Add, a) => linear(&a[0], names).plus(&linear(&a[1], names)),
        Term::Prim(Prim::Sub, a) => linear(&a[0], names).plus(&linear(&a[1], names).scaled(-1)),
        Term::Prim(Prim::Mul, a) => match (&a[0], &a[1]) {
            (Term::Lit(Value::Int(c)), b) | (b, Term::Lit(Value::Int(c))) => {
                linear(b, names).scaled(*c)
            }
            _ => panic!("a product of two names in {t}"),
        },
        _ => panic!("not a linear form: {t}"),
    }
}

/// The test `t` over `names`.
fn cond(t: &Term, names: &[String]) -> Cond {
    let Term::Prim(p, a) = t else {
        panic!("not a test: {t}")
    };
    let diff = |x: &Term, y: &Term| linear(x, names).plus(&linear(y, names).scaled(-1));
    match p {
        Prim::Ge => Cond::AtLeastZero(diff(&a[0], &a[1])),
        Prim::Le => Cond::AtLeastZero(diff(&a[1], &a[0])),
        Prim::Eq => Cond::Zero(diff(&a[0], &a[1])),
        Prim::Or => Cond::Or(Box::new(cond(&a[0], names)), Box::new(cond(&a[1], names))),
        Prim::And => Cond::And(Box::new(cond(&a[0], names)), Box::new(cond(&a[1], names))),
        _ => panic!("not a test the oracle reads: {t}"),
    }
}

/// The least or greatest value of a name over the points found, and a point that gives it,
/// one inside the window when there is one.
struct Extreme {
    value: i64,
    point: Vec<i64>,
    /// Whether `point` lies inside the window, on no edge of it. When no point that gives the
    /// value does, points past the window may extend the end, and the oracle prints it open.
    /// When one does, the end is the end of the window's points only: the windows are chosen
    /// wide enough, and each case that pins an end zedc misses proves it in its comment.
    inside: bool,
}

impl Extreme {
    /// Keeps `point`, which gives `value`, when its value goes past this one's in the
    /// direction `past` (`v < value` for a least value), or equals it and is inside where this
    /// one is not.
    fn update(
        e: &mut Option<Extreme>,
        value: i64,
        point: &[i64],
        inside: bool,
        past: fn(i64, i64) -> bool,
    ) {
        let keep = e
            .as_ref()
            .is_none_or(|e| past(value, e.value) || (value == e.value && inside && !e.inside));
        if keep {
            *e = Some(Extreme {
                value,
                point: point.to_vec(),
                inside,
            });
        }
    }
}

/// What the oracle found of one name: the values points of the window give it, and its
/// least and greatest values.
struct Seen {
    lo: i64,
    /// `values[v - lo]`: whether some point gives the name `v`.
    values: Vec<bool>,
    least: Option<Extreme>,
    most: Option<Extreme>,
}

/// A name that one test, `a >= l` with `l` free of `a`, alone mentions: every value from the
/// least `l` of a point up is the name's, so the oracle lists the other names only.
struct Hub {
    name: Arc<str>,
    /// `l`, over the oracle's names.
    bound: Linear,
    /// The least `l` of a point.
    least: Option<Extreme>,
}

/// The oracle's answer for one family: the points of the window that meet every test.
struct Oracle {
    names: Vec<String>,
    window: Vec<(i64, i64)>,
    seen: Vec<Seen>,
    hub: Option<Hub>,
    points: u64,
}

impl Oracle {
    /// Lists every point of `window` and keeps those that meet `tests`. A name of the scope
    /// that `window` leaves out must be one no test mentions, or the hub of a star (see
    /// [`Hub`]).
    fn of(scope_names: &[Arc<str>], tests: &[Term], window: &[(String, i64, i64)]) -> Oracle {
        let mut names: Vec<String> = window.iter().map(|(n, _, _)| n.clone()).collect();
        // The hub: a scope name outside the window, read as a name of the window first.
        let hub_name = scope_names
            .iter()
            .find(|n| !names.iter().any(|m| **m == ***n) && tests.iter().any(|t| reads(t, n)));
        if let Some(h) = hub_name {
            names.push(h.to_string());
        }
        let mut conds: Vec<Cond> = tests.iter().map(|t| cond(t, &names)).collect();
        let hub = hub_name.map(|h| {
            let i = names.len() - 1;
            let at: Vec<usize> = (0..conds.len()).filter(|&c| conds[c].mentions(i)).collect();
            let [c] = at[..] else {
                panic!("{h} is read by {} tests, not by the one star", at.len())
            };
            let Cond::AtLeastZero(l) = conds.remove(c) else {
                panic!("{h} is read by a test that is not `{h} >= l`")
            };
            assert_eq!(l.coef[i], 1, "{h} is read by a test that is not `{h} >= l`");
            let mut bound = l.scaled(-1);
            bound.coef[i] = 0;
            bound.coef.pop();
            Hub {
                name: h.clone(),
                bound,
                least: None,
            }
        });
        if hub.is_some() {
            names.pop();
            conds.iter_mut().for_each(drop_last);
        }
        let window: Vec<(i64, i64)> = window.iter().map(|&(_, lo, hi)| (lo, hi)).collect();
        let mut o = Oracle::empty(names, window, hub);
        let window = o.window.clone();
        each_point(&window, |point| {
            if conds.iter().all(|c| c.holds(point)) {
                o.see(point);
            }
        });
        o
    }

    /// The oracle of `names` over `window` before it sees any point.
    fn empty(names: Vec<String>, window: Vec<(i64, i64)>, hub: Option<Hub>) -> Oracle {
        Oracle {
            seen: window
                .iter()
                .map(|&(lo, hi)| Seen {
                    lo,
                    values: vec![false; (hi - lo + 1) as usize],
                    least: None,
                    most: None,
                })
                .collect(),
            names,
            window,
            hub,
            points: 0,
        }
    }

    fn see(&mut self, point: &[i64]) {
        self.points += 1;
        let inside = (point.iter().zip(&self.window)).all(|(v, (lo, hi))| lo < v && v < hi);
        for (i, s) in self.seen.iter_mut().enumerate() {
            let v = point[i];
            s.values[(v - s.lo) as usize] = true;
            Extreme::update(&mut s.least, v, point, inside, |a, b| a < b);
            Extreme::update(&mut s.most, v, point, inside, |a, b| a > b);
        }
        if let Some(h) = &mut self.hub {
            Extreme::update(&mut h.least, h.bound.at(point), point, inside, |a, b| a < b);
        }
    }

    /// The oracle's facts of the scope's names, as [`facts`] prints them: the values found,
    /// with an end printed open when only points on the window's edge give it (see
    /// [`Extreme`]); a hub from its least bound up; every integer for a name no test mentions.
    fn facts(&self, scope_names: &[Arc<str>]) -> String {
        if self.points == 0 {
            return "bottom".into();
        }
        let one = |n: &Arc<str>| -> String {
            if let Some(h) = self.hub.as_ref().filter(|h| h.name == *n) {
                return match &h.least {
                    Some(e) if e.inside => format!("[{}..]", e.value),
                    _ => "[..]".into(),
                };
            }
            let Some(i) = self.names.iter().position(|m| **m == **n) else {
                return "[..]".into();
            };
            let s = &self.seen[i];
            let open = |e: &Option<Extreme>| e.as_ref().is_some_and(|e| !e.inside);
            let mut pieces: Vec<(End, End)> = Vec::new();
            let mut start = None;
            for (d, &on) in s.values.iter().chain([&false]).enumerate() {
                let v = s.lo + d as i64;
                match (on, start) {
                    (true, None) => start = Some(v),
                    (false, Some(b)) => {
                        pieces.push((End::of(b), End::of(v - 1)));
                        start = None;
                    }
                    _ => {}
                }
            }
            if open(&s.least) {
                pieces[0].0 = End::NegInf;
            }
            if open(&s.most) {
                let last = pieces.len() - 1;
                pieces[last].1 = End::PosInf;
            }
            let set = IntervalSet::from_pieces(pieces);
            let found: Vec<i64> = (s.values.iter().enumerate())
                .filter(|(_, on)| **on)
                .map(|(d, _)| s.lo + d as i64)
                .collect();
            let modulus = found.iter().fold(0, |g, v| gcd(g, v - found[0]));
            if found.len() <= 1 || modulus == 1 {
                set.to_string()
            } else {
                format!("{set} {} mod {modulus}", found[0].rem_euclid(modulus))
            }
        };
        scope_names
            .iter()
            .map(|n| format!("{n}={}", one(n)))
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// Panics, naming `what`, unless `s` holds every point the oracle found: each name's every
    /// value in its product, and the points of each name's least and greatest values (with the
    /// hub at its least) in the scope with its relation.
    fn check_sound(&self, what: &str, s: &Scope, got: &str) {
        if self.points == 0 {
            return;
        }
        assert!(
            !s.bottom,
            "{what}: the scope is bottom, but {} points meet the tests",
            self.points
        );
        for (i, seen) in self.seen.iter().enumerate() {
            let p = s.get(&self.names[i]);
            for (d, on) in seen.values.iter().enumerate() {
                let v = seen.lo + d as i64;
                assert!(
                    !on || p.contains(&Value::Int(v)),
                    "{what}: {}={v} meets the tests, but the scope gives {got}",
                    self.names[i]
                );
            }
            for e in [&seen.least, &seen.most].into_iter().flatten() {
                let env = self.env(&e.point);
                assert!(
                    s.contains(&env),
                    "{what}: the point {env:?} meets the tests and is not in the scope, which \
                     gives {got} with the relation {}",
                    s.relation
                );
            }
        }
        if let Some(Hub {
            name,
            least: Some(e),
            ..
        }) = &self.hub
        {
            let p = s.get(name);
            let l = e.value;
            for v in [l, l + 1, l + 1_000_000] {
                assert!(
                    p.contains(&Value::Int(v)),
                    "{what}: {name}={v} meets the tests, but the scope gives {got}"
                );
            }
            let mut env = self.env(&e.point);
            env.insert(name.clone(), Value::Int(l));
            assert!(
                s.contains(&env),
                "{what}: the point {env:?} meets the tests and is not in the scope, which gives \
                 {got} with the relation {}",
                s.relation
            );
        }
    }

    /// Whether `s` gives each name of the oracle the least and the greatest value the oracle
    /// prints, and is bottom exactly when no point meets the tests.
    fn ends_of(&self, s: &Scope) -> bool {
        if self.points == 0 || s.bottom {
            return self.points == 0 && s.bottom;
        }
        let end = |e: &Option<Extreme>, open: End| match e {
            Some(e) if e.inside => End::of(e.value),
            _ => open,
        };
        self.names.iter().zip(&self.seen).all(|(n, seen)| {
            let p = s.get(n);
            let ints = p.ints();
            let (Some(first), Some(last)) = (ints.first(), ints.last()) else {
                return false;
            };
            first.0 == end(&seen.least, End::NegInf) && last.1 == end(&seen.most, End::PosInf)
        })
    }

    fn env(&self, point: &[i64]) -> BTreeMap<Arc<str>, Value> {
        (self.names.iter())
            .zip(point)
            .map(|(n, v)| (Arc::from(n.as_str()), Value::Int(*v)))
            .collect()
    }
}

/// Calls `f` on every point of `window`, the first name moving fastest.
fn each_point(window: &[(i64, i64)], mut f: impl FnMut(&[i64])) {
    let mut point: Vec<i64> = window.iter().map(|w| w.0).collect();
    if point.is_empty() {
        return;
    }
    loop {
        f(&point);
        let mut i = 0;
        loop {
            if i == point.len() {
                return;
            }
            if point[i] < window[i].1 {
                point[i] += 1;
                break;
            }
            point[i] = window[i].0;
            i += 1;
        }
    }
}

/// Whether `t` reads the name `n`.
fn reads(t: &Term, n: &str) -> bool {
    match t {
        Term::Var(m) => **m == *n,
        Term::Prim(_, a) => a.iter().any(|a| reads(a, n)),
        _ => false,
    }
}

/// `c` without its last name, whose coefficients are all 0.
fn drop_last(c: &mut Cond) {
    match c {
        Cond::AtLeastZero(l) | Cond::Zero(l) => {
            l.coef.pop();
        }
        Cond::Or(a, b) | Cond::And(a, b) => {
            drop_last(a);
            drop_last(b);
        }
    }
}

fn gcd(a: i64, b: i64) -> i64 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// Checks family `name` at size `k`: the scope holds every point the oracle finds, and the
/// scope's facts and the oracle's are `want` and `exact`. Where the two differ the case
/// pins a fact the oracle finds and the scope misses.
fn check(name: &str, k: usize, want: &str, exact: &str) {
    let f = family(name, k);
    let s = run(&f);
    let got = facts(&s, &f.names);
    let o = Oracle::of(&f.names, &f.tests, &f.window);
    let what = format!("{name} at k = {k}");
    o.check_sound(&what, &s, &got);
    let found = o.facts(&f.names);
    assert_eq!(
        (got.as_str(), found.as_str()),
        (want, exact),
        "{what}: the scope's facts and the oracle's"
    );
}

/// The names of the audit.
const AUDIT_NAMES: [&str; 4] = ["a", "x", "y", "z"];

/// The tests of the review's audit: for each of 128 seeds, 9 tests of atoms `u + c * v >= d`
/// or `u + c * v == d` over the audit's names, drawn in order from one generator, so that a
/// seed's tests depend on every seed before it.
fn audit_tests() -> Vec<Vec<Term>> {
    let mut r = 137_u64;
    let mut next = move || {
        r = r.wrapping_mul(6364136223846793005).wrapping_add(1);
        r >> 32
    };
    let mut atom = move || {
        let u = AUDIT_NAMES[(next() % 4) as usize];
        let v = AUDIT_NAMES[(next() % 4) as usize];
        let c = (next() % 7) as i64 - 3;
        let d = (next() % 9) as i64 - 4;
        let t = add(var(u), times(c, v));
        if next() % 5 == 0 {
            eq(t, int(d))
        } else {
            ge(t, int(d))
        }
    };
    (0..128_u64)
        .map(|seed| {
            (0..9)
                .map(|step| match (seed + step) % 4 {
                    0 => atom(),
                    1 => or(atom(), atom()),
                    2 => or(and(atom(), atom()), atom()),
                    _ => and(or(atom(), atom()), or(atom(), atom())),
                })
                .collect()
        })
        .collect()
}

/// One record of the audit: the scope's facts after a step and the oracle's.
struct Record {
    seed: u64,
    step: usize,
    got: String,
    found: String,
    /// Whether the scope gives each name the least and the greatest value the oracle does.
    ends: bool,
}

/// The records of `seeds`, each checked for soundness. An even seed first bounds every name
/// to `-8..=8`, and the oracle lists `-9..=9` for each name, which holds every point; an odd
/// seed bounds none, and the oracle lists `-12..=12`, so that its facts are those of the
/// window only. Steps 2, 5 and 8 join the scopes of the test and of its negation, which
/// leaves the points as they were; the other steps assume the test.
fn audit(seeds: std::ops::Range<u64>) -> Vec<Record> {
    let all = audit_tests();
    let p = Premises::new();
    let ns: Vec<Arc<str>> = AUDIT_NAMES.into_iter().map(Arc::from).collect();
    let names: Vec<String> = AUDIT_NAMES.map(String::from).to_vec();
    let mut out = Vec::new();
    for seed in seeds {
        let even = seed % 2 == 0;
        let r = if even { 9 } else { 12 };
        let window = vec![(-r, r); 4];
        let mut s = ints(&ns);
        let mut points: Vec<[i64; 4]> = Vec::new();
        each_point(&window, |pt| {
            if !even || pt.iter().all(|v| v.abs() <= 8) {
                points.push(pt.try_into().expect("a point of four names"));
            }
        });
        if even {
            for n in &ns {
                s = s.assume(&and(ge(var(n), int(-8)), le(var(n), int(8))), true, &p);
            }
        }
        for (step, t) in all[seed as usize].iter().enumerate() {
            if step % 3 == 2 {
                s = s.assume(t, true, &p).join(&s.assume(t, false, &p));
            } else {
                s = s.assume(t, true, &p);
                let c = cond(t, &names);
                points.retain(|pt| c.holds(pt));
            }
            let mut o = Oracle::empty(names.clone(), window.clone(), None);
            points.iter().for_each(|pt| o.see(pt));
            let got = facts(&s, &ns);
            o.check_sound(&format!("audit {seed}:{step}"), &s, &got);
            let ends = o.ends_of(&s);
            out.push(Record {
                seed,
                step,
                found: o.facts(&ns),
                ends,
                got,
            });
        }
    }
    out
}

/// [`check`] for a case on which the scope and the oracle agree.
fn exact(name: &str, k: usize, want: &str) {
    check(name, k, want, want);
}

#[test]
fn armlink_against_the_oracle() {
    exact("armlink", 1, "a=[..] x=[..] y=[..=4, 100..]");
}

#[test]
fn armlink2_against_the_oracle() {
    exact("armlink2", 1, "a=[..] x=[..] y=[..=4, 100..=990]");
}

#[test]
fn armlink3_against_the_oracle() {
    exact("armlink3", 1, "a=[..] x=[..] y=[..]");
}

#[test]
fn boxstar_against_the_oracle() {
    exact("boxstar", 1, "a=[-7..] x=[-3..=4] y=[-4..=4]");
    exact("boxstar", 2, "a=[-15..] x=[-7..=8] y=[-8..=8]");
    exact("boxstar", 3, "a=[-23..] x=[-11..=12] y=[-12..=12]");
}

#[test]
fn chain_against_the_oracle() {
    exact("chain", 1, "a=[-7..] x=[-3..=3] y=[-4..=-1, 1..=4]");
    exact("chain", 2, "a=[-15..] x=[-7..=6] y=[-8..=-2, 2..=8]");
    exact("chain", 3, "a=[-23..] x=[-11..=9] y=[-12..=-2, 2..=12]");
}

#[test]
fn upper_release_against_the_oracle() {
    // When the threshold aggregate stops holding, the upper disjunction it read is projected
    // by itself again, as the step is.
    exact("upper_release", 1, "a=[..] x=[..] y=[..=-1]");
}

#[test]
fn drop_end_against_the_oracle() {
    // A disjunction is projected in a case when an arm bounds an end only through a name
    // whose end is finite (`y == z - 1` with `y >= -8`).
    exact("drop_end", 1, "a=[-8..=3] x=[-7..=8] y=[-8..=8] z=[-8..=8]");
}

#[test]
fn unary_arms_against_the_oracle() {
    // Each `zi` is at least 1 or at most -1; `x` is free, since `z0 + z(k-1) >= 5` holds
    // when every `zi` is 5.
    for k in 2..=3 {
        let zs: String = (0..k).map(|i| format!(" z{i}=[..=-1, 1..]")).collect();
        exact("unary_arms", k, &format!("a=[..] x=[..] y=[..]{zs}"));
    }
}

#[test]
fn coord3_against_the_oracle() {
    // `y <= 4`: for `y >= 5` the step gives `x >= 10`, so `x + y >= 15` and `x + 2 * y >= 20`,
    // and neither arm of the last test holds; (10, 4) meets every test. The threshold
    // aggregate finds it from the last test's arms (LAZY-hub-unsolved).
    exact("coord3", 1, "a=[..] x=[..] y=[..=4]");
}

#[test]
fn coordkk_against_the_oracle() {
    // `y <= -2k`: for `y > -1000 + k` the steps give `x >= k`, and the last test
    // then gives `y <= -k - x <= -2k` or `y <= -2500 - k / 2`; for `y <= -1000 + k` the bound
    // holds already. (k, -2k) meets every test.
    for k in 1..=3 {
        let y = -2 * k as i64;
        exact("coordkk", k, &format!("a=[..] x=[..] y=[..={y}]"));
    }
}

#[test]
fn coordkk_y_against_the_oracle() {
    // `y <= -2k`, as on coordkk.
    for k in 1..=3 {
        let y = -2 * k as i64;
        exact("coordkk_y", k, &format!("a=[..] x=[..] y=[..={y}]"));
    }
}

#[test]
fn coordmix_against_the_oracle() {
    // `y <= -k`: for `y > -10k` the step gives `x >= 0`, and the last test then gives
    // `y <= -k - x` or `y <= (-51k - x) / 2`; for `y <= -10k` the bound holds already.
    // (0, -k) meets every test.
    for k in 1..=3 {
        exact("coordmix", k, &format!("a=[..] x=[..] y=[..=-{k}]"));
    }
}

#[test]
fn coordmix_floor_against_the_oracle() {
    exact("coordmix_floor", 1, "a=[..] x=[-299..=149] y=[-100..=-1]");
    exact("coordmix_floor", 2, "a=[..] x=[-599..=298] y=[-200..=-2]");
    exact("coordmix_floor", 3, "a=[..] x=[-899..=447] y=[-300..=-3]");
}

#[test]
fn coordmix_shift_against_the_oracle() {
    // `y <= floor(-11k / 4)`: for `y > -10k` the step gives `x >= 0` and the last
    // test `x <= -k - y` (its other arm needs `y <= -25k`). The first split then needs
    // `x - 3y >= 10k`, so `-k - 4y >= 10k`; its other arm `x + 3y >= 10k` needs `y >= 5.5k`
    // and so `x < 0`.
    for (k, y) in [(1, -3), (2, -6), (3, -9)] {
        exact("coordmix_shift", k, &format!("a=[..] x=[..] y=[..={y}]"));
    }
}

#[test]
fn coordmix_slopes_against_the_oracle() {
    // `y <= -k`: for `y > -10k` the step gives `x >= 0`, and the last test then gives
    // `y <= -k - x / k` or `y <= -25k - k / 2 - x / (2k)`.
    for k in 1..=3 {
        exact("coordmix_slopes", k, &format!("a=[..] x=[..] y=[..=-{k}]"));
    }
}

#[test]
fn coordmix_unmatched_against_the_oracle() {
    // `y <= -k`: for `y > -10k` the step gives `x >= 0`, and the last test, of slope
    // `q = 2k + 3`, then gives `y <= -k - x / q` or `y <= -(51k + x / q) / 2`.
    for k in 1..=2 {
        exact(
            "coordmix_unmatched",
            k,
            &format!("a=[..] x=[..] y=[..=-{k}]"),
        );
    }
}

#[test]
fn cuts_against_the_oracle() {
    exact("cuts", 1, "a=[-8..] x=[-4..=3] y=[-4..=4]");
    exact("cuts", 2, "a=[-16..] x=[-8..=6] y=[-8..=8]");
    exact("cuts", 3, "a=[-24..] x=[-12..=9] y=[-12..=12]");
}

#[test]
fn exit_order_against_the_oracle() {
    exact("exit_order", 1, "a=[..] x=[1..=1] y=[0..=0]");
}

#[test]
fn hole_families_against_the_oracle() {
    for name in ["hole1", "hole1s", "hole2", "hole2s", "hole2c"] {
        exact(name, 1, "a=[..] x=[..=-9, 10..] y=[..=-9, 10..]");
    }
}

#[test]
fn hole_end0_against_the_oracle() {
    exact("hole_end0", 1, "a=[..] x=[0..=10] y=[0..=10]");
}

#[test]
fn hole_end1_against_the_oracle() {
    // The hole `6..=8` in `x`. The two hole tests leave `x = 6` only with `y = 5`, and `x` =
    // 7 or 8 only with `y = 10`; the last test needs `x + y <= 10` or `3x + y >= 37`, which
    // fails at (6, 5) (11 and 23), (7, 10) (17 and 31) and (8, 10) (18 and 34). Each case
    // of the last test projects the first hole test with its arm: the arm `x + y <= 10`
    // bounds `x` above in the hole test's last arm, which alone does not.
    exact("hole_end1", 1, "a=[..] x=[0..=5, 9..=10] y=[0..=10]");
}

#[test]
fn hole_end2_against_the_oracle() {
    // With hole_end1's hole `6..=8` and `x <= 8`, the greatest `x` is 5.
    exact("hole_end2", 1, "a=[..] x=[0..=5] y=[0..=10]");
}

/// The padded forms give the same answers: the `k` redundant parts change nothing.
#[test]
fn hole_end_pad_against_the_oracle() {
    for k in [1, 4] {
        exact("hole_end1_pad", k, "a=[..] x=[0..=5, 9..=10] y=[0..=10]");
        exact("hole_end2_pad", k, "a=[..] x=[0..=5] y=[0..=10]");
    }
}

#[test]
fn hop_families_against_the_oracle() {
    for k in 1..=2 {
        exact("hop", k, "a=[8..] x=[0..=1] y=[3..=3] z=[5..=5]");
        exact("hopon", k, "a=[8..] x=[0..=0] y=[3..=3] z=[5..=5]");
        for name in ["hopb", "hoponb"] {
            exact(
                name,
                k,
                "a=[-2000..] x=[0..=1] y=[-1000..=1000] z=[-1000..=1000]",
            );
        }
    }
}

#[test]
fn hubs_against_the_oracle() {
    for k in 1..=3 {
        exact("hubs", k, "a=[..] x=[..] y=[..]");
    }
}

#[test]
fn m1_trans_ce_against_the_oracle() {
    // `a <= 0`: with `a > 0` the second test gives `y >= 5`, the step `x >= 10`, so
    // `x + y >= 15`, and the last test's other arm needs `a <= 0`.
    exact("m1_trans_ce", 1, "a=[..=0] x=[..] y=[..]");
}

#[test]
fn persist_against_the_oracle() {
    exact("persist", 1, "a=[-1000..] x=[..] y=[..]");
    exact("persist", 2, "a=[-666..] x=[..] y=[..]");
}

#[test]
fn rows_one_pair_against_the_oracle() {
    for k in 1..=4 {
        exact("rows_one_pair", k, "a=[..] x=[..] y=[..]");
    }
}

#[test]
fn side_families_against_the_oracle() {
    for name in ["side1", "side2", "side3"] {
        exact(name, 1, "a=[..=-9] x=[..=5] y=[..=-9]");
    }
    exact("side5", 1, "a=[..] x=[..=-6] y=[..=-9]");
    // `y <= 4`, as on coord3, and from it `a <= 4` by the part `a <= y || a <= -50`.
    exact("side4", 1, "a=[..=4] x=[..] y=[..=4]");
}

#[test]
fn stair_cover_against_the_oracle() {
    for k in 1..=2 {
        exact("stair_cover", k, "a=[..] x=[0..=1000] y=[0..=1000]");
    }
    for k in 1..=3 {
        exact("stair_cover_free", k, "a=[..] x=[..] y=[..]");
    }
}

#[test]
fn stair_holes_against_the_oracle() {
    let want = [
        "a=[..] x=[..=5, 10..] y=[..=2, 7..]",
        "a=[..] x=[..=5, 10..=15, 20..] y=[..=-8, -3..=2, 7..]",
        "a=[..] x=[..=5, 10..=15, 20..=25, 30..] y=[..=-18, -13..=-8, -3..=2, 7..]",
    ];
    for name in ["stair_holes", "stair_holes_mix", "stair_holes_late"] {
        for (k, want) in (1..).zip(want) {
            exact(name, k, want);
        }
    }
}

#[test]
fn stair_hull_against_the_oracle() {
    exact("stair_hull", 1, "a=[..] x=[-8..=8] y=[-8..=3]");
    exact("stair_hull_vertices", 1, "a=[..] x=[-8..=8] y=[-8..=4]");
}

#[test]
fn star_families_against_the_oracle() {
    for k in 1..=3 {
        for name in ["star", "star_extra", "starjoin"] {
            exact(name, k, "a=[..] x=[..] y=[..]");
        }
    }
    for k in 1..=2 {
        exact("star_mixed", k, "a=[..] x=[..] y=[..]");
    }
}

#[test]
fn wide_against_the_oracle() {
    exact("wide", 1, "a=[..] x=[..] y=[..] z0=[-1000..=-1, 1..]");
    exact("wide_pairs", 1, "a=[..] x=[..] y=[..] z0=[0..]");
    for k in 2..=4 {
        let z: String = (0..k).map(|j| format!(" z{j}=[..]")).collect();
        exact("wide", k, &format!("a=[..] x=[..] y=[..]{z}"));
        exact("wide_pairs", k, &format!("a=[..] x=[..] y=[..]{z}"));
    }
}

/// The audit's records of the even seeds `seeds`, checked for soundness, and how many give
/// every name the oracle's least and greatest values (`ends`) and how many give the oracle's
/// facts in full (`equal`). The odd seeds' records are checked for soundness only: their
/// window is not every point.
fn audit_counts(seeds: std::ops::Range<u64>, ends: usize, equal: usize) {
    let even: Vec<Record> = audit(seeds)
        .into_iter()
        .filter(|r| r.seed % 2 == 0)
        .collect();
    let got = (
        even.iter().filter(|r| r.ends).count(),
        even.iter().filter(|r| r.got == r.found).count(),
    );
    assert_eq!(
        got,
        (ends, equal),
        "records with the oracle's ends and facts"
    );
}

#[test]
fn audit_seeds_0_to_31() {
    audit_counts(0..32, 134, 110);
}

#[test]
fn audit_seeds_32_to_63() {
    audit_counts(32..64, 128, 114);
}

#[test]
fn audit_seeds_64_to_95() {
    audit_counts(64..96, 130, 116);
}

#[test]
fn audit_seeds_96_to_127() {
    audit_counts(96..128, 136, 119);
}

/// The record of the audit at `seed` and `step`, as the scope and the oracle give it.
fn record(seed: u64, step: usize) -> (String, String) {
    let r = audit(seed..seed + 1)
        .into_iter()
        .nth(step)
        .expect("each seed has 9 steps");
    assert_eq!((r.seed, r.step), (seed, step), "the record's place");
    (r.got, r.found)
}

/// Audit record 85:8 (85:7 is the same): `y >= -1`, which the tests up to step 7 prove and
/// (a, x, y, z) = (1, -1, -1, -1) attains, found by a part whose arms bound `y` only with
/// rows derived through what it is projected with (LAZY-hub-unsolved). Seed 85 is odd, so the
/// oracle lists `-12..=12` only; its `z <= 5` comes from step 7's `y - 2z >= 1` with `y <= 12`
/// and is not a fact of the unbounded names.
#[test]
fn audit_record_85_8() {
    assert_eq!(
        record(85, 8),
        (
            "a=[..] x=[..] y=[-1..] z=[..]".into(),
            "a=[..] x=[..] y=[-1..] z=[..=5]".into()
        )
    );
}

/// Audit record 108:3: `x >= -7`, found as in the family drop_end. Step 0 bounds `a <= 3` in the
/// box `-8..=8`, so at `x = -8` the first part of step 3 needs `x == z`, and its second part
/// `z >= 2a`, so `a <= -4`; step 1 then needs `z - y == 1`, so `y = -9`, outside the box.
#[test]
fn audit_record_108_3() {
    assert_eq!(
        record(108, 3),
        (
            "a=[-8..=3] x=[-7..=8] y=[-8..=8] z=[-8..=8]".into(),
            "a=[-8..=3] x=[-7..=8] y=[-8..=8] z=[-8..=8]".into()
        )
    );
}

/// Audit record 115:3: `y >= -3`. Step 3's first arm gives it directly; its second arm
/// `y >= 2z + 2`, with steps 0 and 1, gives `y >= 3`.
#[test]
fn audit_record_115_3() {
    assert_eq!(
        record(115, 3),
        (
            "a=[..] x=[..] y=[-3..] z=[..]".into(),
            "a=[..] x=[..] y=[-3..] z=[..]".into()
        )
    );
}

/// Holds the work of the reduced product on family `name` to order `k^power` from `k = n` to
/// `8n`, the family's tests built before the work is measured.
fn scales(name: &str, n: usize, power: u32) {
    let made = scaling::inputs(n, |k| family(name, k));
    scaling::check_order(&format!("the family {name}"), n, power, |k| {
        run(&made[&k]);
    });
}

#[test]
fn star_scales() {
    scales("star", 8, 1);
}

#[test]
fn star_mixed_scales() {
    scales("star_mixed", 8, 1);
}

#[test]
fn starjoin_scales() {
    scales("starjoin", 8, 1);
}

#[test]
fn hubs_scale() {
    scales("hubs", 8, 1);
}

#[test]
fn coordmix_scales() {
    scales("coordmix", 8, 1);
}

#[test]
fn coordmix_shift_scales() {
    scales("coordmix_shift", 8, 1);
}

#[test]
fn coordmix_unmatched_scales() {
    scales("coordmix_unmatched", 8, 1);
}

#[test]
fn hole_end1_pad_scales() {
    scales("hole_end1_pad", 8, 1);
}

#[test]
fn hole_end2_pad_scales() {
    scales("hole_end2_pad", 8, 1);
}

#[test]
fn rows_one_pair_scales() {
    scales("rows_one_pair", 8, 1);
}

#[test]
fn wide_pairs_scale() {
    scales("wide_pairs", 8, 1);
}

#[test]
fn drop_ends_scale() {
    scales("drop_ends", 8, 1);
}

#[test]
fn unary_arms_scale() {
    scales("unary_arms", 8, 1);
}

#[test]
#[ignore = "PERF-l139-under9: cuts, 11.1 times the instructions (315.9M and 3,501.2M) and 11.0 times the bytes (59.9M and 662.0M) at 8n on origin/main 783fd27c8, over the limit of 10.5; open"]
fn cuts_scale() {
    scales("cuts", 4, 1);
}

/// Each of wide's `k + 1` tests holds a sum of `k` names, so its input has `k^2` terms: order
/// `k^2` is linear in the input.
#[test]
fn wide_scales() {
    scales("wide", 8, 2);
}

#[test]
#[ignore = "PERF-l139-under9: coordmix_floor, 12.1 times the instructions (219.8M and 2,654.8M) and 10.7 times the bytes (41.1M and 438.9M) at 8n on origin/main 783fd27c8, over the limit of 10.5; open"]
fn coordmix_floor_scales() {
    scales("coordmix_floor", 4, 1);
}

/// About `k^1.6` to `k^2` on main; about `k^1.1` to `k^1.25` since the threshold aggregate
/// reads the upper disjunctions (LAZY-hub-unsolved).
#[test]
fn coordkk_y_scales() {
    scales("coordkk_y", 8, 1);
}

/// About `k^1.8` to `k^2.1` on main; about `k^1.05` to `k^1.1` since the threshold aggregate
/// reads the upper disjunctions and every ray of a group (LAZY-hub-unsolved).
#[test]
fn coordmix_slopes_scales() {
    scales("coordmix_slopes", 4, 1);
}

/// About `k^1.2` to `k^1.8` from `k = 8` to 128 on main; with the threshold aggregate's
/// upper disjunctions (LAZY-hub-unsolved), about `k^1.2` to `k^1.4`, 15.6 times the work from
/// `k = 16` to 128 against the limit 15.4. Each of the `k` tests took one constraint on two
/// names out of a block of near `k` such constraints, and the work after it read every
/// conjunct of that block: the names of each (`Scope::due`) and a search through it
/// (`Blocks::peel`). Now the names of a block and its constraints on two names are counted as
/// they come and go (`Blocks::names_of`, `Blocks::cut`), and the blocks a block went to are
/// read from the difference of its persistent sets (`Blocks::now_of`): 9.6 times the work
/// (106M and 1,017M instructions; 113.6M and 1,768M, 15.6 times, before) and 8.4 times the
/// bytes (PERF-l139-family, COMPLEXITY.md PERF-l139-due).
#[test]
fn coordkk_scales() {
    scales("coordkk", 16, 1);
}

// The families below grow faster than linearly on main (TESTS-lhx-families, 2026-11-11, the
// power per doubling of `k` as measured): each is held to order `k` and ignored with the item
// that would fix it. The profile is the same for all (PERF-l139-family, 2026-11-12): the time
// is in the projection of parts (`Scope::project_part`, 69 to 100 per cent at `n` and at
// `8n`, 29 to 91 per cent in `hull_from`), and the parts stay small; what grows is the number
// of projections, near `k^1.7` to `k^1.9` from `k = 4` to 16. Each time the interval of a
// name moves, mostly in the copies of the scope that `cases` makes for the arms of a
// disjunction, every part that mentions the name is projected again (`Scope::project_block`
// wakes `due_users`), near `k` parts each time, and almost none of them changes. stair_holes
// also projects each part in time near `k`, as `x` carries near `k` holes. Waking only the
// parts whose result can change needs, for each part, the ends of its names its result
// depends on; a part with a constraint on several names in its base, or with holes, has no
// such ends, so the fix is open (cross-review).
//
// Since PERF-l139-wake (2026-11-13) a part already projected is skipped when a test shows
// that every value of each of its names has an integer point of the part (`Scope::idle`,
// Fourier-Motzkin elimination with the dark shadow of Pugh 1991, on rows whose count never
// grows), and other tests skip a punctured line with support at every value
// (`Scope::puncture_idle`) and the parts of lower threshold clauses under one upper sum
// (`LowerGaps`); `extreme_base` and `compact_abs` drop rows that other rows imply. The
// families below then pass under 13 at 8n, measured as instructions and bytes of the first
// runs: stair_holes 7.4 and 6.2, stair_holes_mix 7.4 and 6.2, stair_cover 8.2 and 6.6,
// stair_cover_free 8.8 and 7.2, stair_holes_late 9.7 and 8.5, hop 10.7 and 10.0, hopon 11.6
// and 10.8, boxstar 11.5 and 10.8, cuts 11.2 and 11.1, coordmix_floor 12.3 and 10.7, hoponb
// 12.9 and 12.1. star_extra, persist, hopb and chain stay ignored (chain was 12.9 on abf5d24cd
// and is 13.1 on af6a5a696).
//
// Since the limit fell from 13 to 10.5 (TESTS-scaling-limit-10_5, 2026-11-13), six of them are
// over it at 8n, measured on the first runs on 783fd27c8 as instructions and bytes: hop 10.6 and
// 10.0, cuts 11.1 and 11.0, boxstar 11.4 and 10.8, hopon 11.5 and 10.8, coordmix_floor 12.1 and
// 10.7, hoponb 12.8 and 12.0. Each is ignored with PERF-l139-under9, the item that would bring
// it under 9 (RED-l139-six); stair_holes_late passes.
//
// Since PERF-l139-family (2026-11-13) the solver asks each side of a hull first at the real
// bound of its rows (`hull_side`), and hop and hopon pass again, at 8.9 and 8.5 (hop) and 9.8
// and 9.4 (hopon) times the instructions and bytes at 8n; the questions for sides such as
// `(1000 + c) / i` of hopb no longer grow with the tests.

/// About `k^1.75` to `k^1.96`.
#[test]
#[ignore = "PERF-l139-family: star_extra, 16.2 times the instructions at 8n (117.3M and 1,904.8M), over the limit of 13; open"]
fn star_extra_scales() {
    scales("star_extra", 4, 1);
}

/// About `k^1.7` from `k = 8` to 32. At `n = 2` the limit's log factor is 4, and main
/// passes (31.9 times the work against 35.2); at `n = 4` each run of `k = 32` takes over 30 s,
/// so the test would not finish in 60 s.
#[test]
#[ignore = "PERF-l139-family: chain, 13.1 times the instructions at 8n (352.6M and 4,633.1M) on origin/main af6a5a696, over the limit of 13 (12.9 on abf5d24cd); open"]
fn chain_scales() {
    scales("chain", 2, 1);
}

/// About `k^2.1`.
#[test]
#[ignore = "PERF-l139-under9: boxstar, 11.4 times the instructions (144.7M and 1,648.4M) and 10.8 times the bytes (27.9M and 300.3M) at 8n on origin/main 783fd27c8, over the limit of 10.5; open"]
fn boxstar_scales() {
    scales("boxstar", 2, 1);
}

/// About `k^2.5` from `k = 8` to 16.
#[test]
#[ignore = "PERF-l139-family: persist, 13.2 times the bytes at 8n (39.3M and 517.3M), over the limit of 13; open"]
fn persist_scales() {
    scales("persist", 2, 1);
}

/// About `k^2.7` to `k^2.8` on stair_holes and stair_holes_mix, and `k^2` on
/// stair_holes_late.
#[test]
fn stair_holes_scale() {
    scales("stair_holes", 4, 1);
}

#[test]
fn stair_holes_mix_scales() {
    scales("stair_holes_mix", 4, 1);
}

#[test]
fn stair_holes_late_scales() {
    scales("stair_holes_late", 8, 1);
}

/// About `k^2`.
#[test]
fn stair_cover_scales() {
    scales("stair_cover", 8, 1);
}

#[test]
fn stair_cover_free_scales() {
    scales("stair_cover_free", 8, 1);
}

/// About `k^2` from `k = 8` to 16, each run of `k = 16` some 60 billion instructions.
#[test]
fn hop_scales() {
    scales("hop", 2, 1);
}

#[test]
fn hopon_scales() {
    scales("hopon", 2, 1);
}

#[test]
#[ignore = "PERF-l139-family: hopb, 13.0 times the instructions at 8n (152.3M and 1,981.7M), at the limit of 13; open"]
fn hopb_scales() {
    scales("hopb", 2, 1);
}

#[test]
#[ignore = "PERF-l139-under9: hoponb, 12.8 times the instructions (186.7M and 2,388.3M) and 12.0 times the bytes (34.6M and 416.7M) at 8n on origin/main 783fd27c8, over the limit of 10.5; open"]
fn hoponb_scales() {
    scales("hoponb", 2, 1);
}

#[test]
fn two_eq_case_against_the_oracle() {
    // A lost bound, kept as it is: in the part `a <= 2`, `a == 2 * z1 + 1` alone gives
    // `z1 <= 0` and `b <= 4`; `b <= 2` needs `a <= -3`, which takes both equalities with
    // rounding between them, and the part's `z1 <= -2` does not reach `b` (PRODUCT-two-eq-round).
    // The rule that one equality of two names per name is added to the part's rows is not
    // the cause: with every such equality added, `b <= 4` still.
    let k0 =
        "a=[..=-3, 9..=39, 45..] b=[..=4, 8..] z0=[..=-1, 3..=13, 15..] z1=[..=-2, 4..=19, 22..]";
    let k1 = "a=[..=-3, 9..] b=[..=4, 8..] z0=[..=-1, 3..] z1=[..=-2, 4..]";
    for (k, want) in [(0, k0), (1, k1)] {
        check(
            "two_eq_case",
            k,
            want,
            "a=[-3..=-3, 9..=9] 9 mod 12 b=[..=2, 8..=8] z0=[-1..=-1, 3..=3] 3 mod 4 \
             z1=[-2..=-2, 4..=4] 4 mod 6",
        );
    }
}

/// The cases that review rounds of PERF-l139-wake built to break the shortcuts that skip a
/// projection (the integer-witness test of an idle part, the punctured-line support test, the
/// reflected gaps of lower threshold clauses, the unbounded-leaf rays, and the pruned rows
/// of `extreme_base` and `compact_abs`): each case is checked against the oracle, and its
/// facts are those origin/main gave before these shortcuts (abf5d24cd).
#[test]
fn projection_shortcut_cases() {
    fn probe(out: &mut Vec<String>, label: &str, ns: &[&str], steps: Vec<Term>) {
        let ns: Vec<Arc<str>> = ns.iter().map(|n| Arc::from(*n)).collect();
        let p = Premises::new();
        let mut s = ints(&ns);
        for t in &steps {
            s = s.assume(t, true, &p);
        }
        let window: Vec<_> = ns
            .iter()
            .map(|n| {
                (
                    n.to_string(),
                    if &**n == "a" { -10 } else { 0 },
                    if &**n == "a" { 10 } else { 4 },
                )
            })
            .collect();
        Oracle::of(&ns, &steps, &window).check_sound(label, &s, &facts(&s, &ns));
        out.push(format!("{label}: {}", facts(&s, &ns)));
    }
    fn box4(n: &str) -> Term {
        and(ge(var(n), int(0)), le(var(n), int(4)))
    }
    let out = &mut Vec::new();
    // punctured line x != y with x + y = 4 on [0,4]^2: main can remove x = 2
    probe(
        out,
        "P1 eq-then-ne",
        &["x", "y"],
        vec![
            box4("x"),
            box4("y"),
            eq(add(var("x"), var("y")), int(4)),
            or(
                ge(sub(var("x"), var("y")), int(1)),
                le(sub(var("x"), var("y")), int(-1)),
            ),
        ],
    );
    probe(
        out,
        "P2 ne-then-eq",
        &["x", "y"],
        vec![
            box4("x"),
            box4("y"),
            or(
                ge(sub(var("x"), var("y")), int(1)),
                le(sub(var("x"), var("y")), int(-1)),
            ),
            eq(add(var("x"), var("y")), int(4)),
        ],
    );
    probe(
        out,
        "P3 le-ge-sum",
        &["x", "y"],
        vec![
            box4("x"),
            box4("y"),
            le(add(var("x"), var("y")), int(4)),
            ge(add(var("x"), var("y")), int(4)),
            or(
                ge(sub(var("x"), var("y")), int(1)),
                le(sub(var("x"), var("y")), int(-1)),
            ),
        ],
    );
    // hop-shaped with a third name
    probe(
        out,
        "P4 hop3",
        &["x", "y", "z"],
        vec![
            box4("x"),
            box4("y"),
            box4("z"),
            eq(add(var("y"), var("z")), int(4)),
            or(
                le(var("x"), int(0)),
                or(
                    ge(add(var("y"), add(var("z"), var("z"))), int(7)),
                    le(add(var("y"), add(var("z"), var("z"))), int(5)),
                ),
            ),
        ],
    );
    // Opus D-class example
    probe(
        out,
        "D1 x>=3||y>=3, x+y<=4",
        &["x", "y"],
        vec![
            box4("x"),
            box4("y"),
            le(add(var("x"), var("y")), int(4)),
            or(ge(var("x"), int(3)), ge(var("y"), int(3))),
        ],
    );
    // Boundary fibers of a half-plane can be singletons: reject that shortcut.
    for k in 0..=4 {
        probe(
            out,
            &format!("B{k} singleton-edge"),
            &["x", "y"],
            vec![
                box4("x"),
                box4("y"),
                ge(add(var("x"), times(2, "y")), int(8)),
                or(
                    ge(add(var("x"), var("y")), int(k + 5)),
                    le(add(var("x"), var("y")), int(k + 3)),
                ),
            ],
        );
    }
    // A unique minimizer removed by the puncture raises a star's leaf.
    probe(
        out,
        "L1 leaf-minimum",
        &["a", "x", "y"],
        vec![
            box4("x"),
            box4("y"),
            star(),
            or(
                ge(add(var("x"), var("y")), int(1)),
                le(add(var("x"), var("y")), int(-1)),
            ),
        ],
    );
    // Leave a reflected-gap certificate through a third name and a join.
    let ns: Vec<Arc<str>> = ["a", "x", "y"].into_iter().map(Arc::from).collect();
    let p = Premises::new();
    let mut s = ints(&ns);
    for t in [
        le(add(var("x"), var("y")), int(12)),
        or(ge(var("x"), int(10)), ge(var("y"), int(7))),
        or(ge(var("x"), int(20)), ge(var("y"), int(-3))),
        star(),
    ] {
        s = s.assume(&t, true, &p);
    }
    let t = ge(sub(var("x"), var("y")), int(3));
    s = s.assume(&t, true, &p).join(&s.assume(&t, false, &p));
    s = s.assume(&or(ge(var("x"), int(30)), ge(var("y"), int(-13))), true, &p);
    out.push(format!("C1 certificate-exit-join: {}", facts(&s, &ns)));
    // Half-plane orientations, integer breakpoints, and both projection orders.
    for j in [-5, -2, -1, 1, 2, 5] {
        for c in -3..=7 {
            for first in [false, true] {
                let mut steps = vec![box4("x"), box4("y")];
                let row = ge(add(var("x"), times(j, "y")), int(c));
                if first {
                    steps.extend([star(), row]);
                } else {
                    steps.extend([row, star()]);
                }
                probe(out, &format!("U{j},{c},{first}"), &["a", "x", "y"], steps);
            }
        }
    }
    // Rule G (idle parts): a part projected once, then woken by a new base row or a narrowed
    // name. G1/G4: x + 1 <= 3y <= x + 2 has a real y for every x but an integer y only for
    // x in {1, 2, 4} (the dark shadow's slack). G2: y = x where y has a hole at 2. G3: y
    // bounded from below by two rows. G5: x <= 2y <= x + 1 has an integer y for every x.
    let (x, y, z) = (|| var("x"), || var("y"), || var("z"));
    let x5 = || and(ge(x(), int(0)), le(x(), int(5)));
    probe(
        out,
        "G1 shadow, base after part",
        &["x", "y"],
        vec![
            box4("x"),
            box4("y"),
            or(ge(x(), int(100)), le(times(3, "y"), add(x(), int(2)))),
            ge(times(3, "y"), add(x(), int(1))),
        ],
    );
    probe(
        out,
        "G2 hole in eliminated y",
        &["x", "y"],
        vec![
            box4("x"),
            box4("y"),
            or(le(y(), int(1)), ge(y(), int(3))),
            or(ge(x(), int(100)), le(y(), x())),
            ge(y(), x()),
        ],
    );
    probe(
        out,
        "G3 two lower rows",
        &["x", "y", "z"],
        vec![
            box4("x"),
            box4("y"),
            box4("z"),
            or(
                le(x(), int(0)),
                and(
                    ge(add(y(), times(2, "z")), int(7)),
                    ge(add(y(), z()), int(5)),
                ),
            ),
            le(add(y(), z()), int(5)),
            le(x(), int(3)),
        ],
    );
    probe(
        out,
        "G4 shadow, woken by x <= 4",
        &["x", "y"],
        vec![
            x5(),
            box4("y"),
            ge(times(3, "y"), add(x(), int(1))),
            or(ge(x(), int(100)), le(times(3, "y"), add(x(), int(2)))),
            le(x(), int(4)),
        ],
    );
    probe(
        out,
        "G5 x <= 2y <= x + 1",
        &["x", "y"],
        vec![
            x5(),
            box4("y"),
            ge(times(2, "y"), x()),
            or(ge(x(), int(100)), le(times(2, "y"), add(x(), int(1)))),
            le(x(), int(4)),
        ],
    );
    // E1: G5 woken by y >= 1: the low end of y's interval, not a row, keeps x >= 1 once y is
    // eliminated.
    probe(
        out,
        "E1 G5 then y >= 1",
        &["x", "y"],
        vec![
            x5(),
            box4("y"),
            ge(times(2, "y"), x()),
            or(ge(x(), int(100)), le(times(2, "y"), add(x(), int(1)))),
            ge(y(), int(1)),
        ],
    );
    // Audit seed 26, steps 0 to 4 (a join at step 2): a dark shadow with coefficients 2 and 3,
    // where the real shadow leaves x's upper part.
    let ns: Vec<Arc<str>> = AUDIT_NAMES.into_iter().map(Arc::from).collect();
    let (p, mut s) = (Premises::new(), ints(&ns));
    for n in &ns {
        s = s.assume(&and(ge(var(n), int(-8)), le(var(n), int(8))), true, &p);
    }
    for (i, t) in audit_tests()[26].iter().enumerate().take(5) {
        s = if i == 2 {
            s.assume(t, true, &p).join(&s.assume(t, false, &p))
        } else {
            s.assume(t, true, &p)
        };
    }
    out.push(format!("A26 audit seed 26 steps 0-4: {}", facts(&s, &ns)));
    // Classes: x = 2w (or 2w + 1, 3w + 1) gives x a class while x is eliminated or read at a
    // corner in the part, which is projected once and woken by a new base row or y <= 3.
    let b = |n: &str, l: i64, h: i64| and(ge(var(n), int(l)), le(var(n), int(h)));
    let two_y = || add(y(), y());
    probe(
        out,
        "C1 x = 2w, x = 2y + 1",
        &["x", "y", "w"],
        vec![
            b("x", 0, 9),
            b("y", 0, 4),
            b("w", 0, 9),
            eq(x(), times(2, "w")),
            or(ge(y(), int(100)), le(x(), add(two_y(), int(1)))),
            ge(x(), add(two_y(), int(1))),
        ],
    );
    probe(
        out,
        "C2 x = 2w, x = y + 1",
        &["x", "y", "w"],
        vec![
            b("x", 0, 9),
            b("y", 0, 3),
            b("w", 0, 9),
            eq(x(), times(2, "w")),
            or(ge(y(), int(100)), le(x(), add(y(), int(1)))),
            ge(x(), add(y(), int(1))),
        ],
    );
    probe(
        out,
        "C3 x = 2w + 1, x = 2y",
        &["x", "y", "w"],
        vec![
            b("x", 0, 9),
            b("y", 0, 4),
            b("w", 0, 9),
            eq(x(), add(times(2, "w"), int(1))),
            or(ge(y(), int(100)), le(x(), two_y())),
            ge(x(), two_y()),
            le(y(), int(3)),
        ],
    );
    probe(
        out,
        "C4 x = 3w + 1, x >= y",
        &["x", "y", "w"],
        vec![
            b("x", 0, 9),
            b("y", 0, 4),
            b("w", 0, 9),
            eq(x(), add(times(3, "w"), int(1))),
            or(ge(y(), int(100)), ge(x(), y())),
            le(y(), int(3)),
        ],
    );
    let want = WANT_SHORTCUT_CASES.trim();
    assert_eq!(out.join("\n"), want);
}

/// The facts of [`projection_shortcut_cases`] on origin/main 9568d1a8d, the same as on abf5d24cd
/// except C2, where main now gives x = 2 or 4 (x = 2w, w in 1..=2) for the interval 2..=4.
const WANT_SHORTCUT_CASES: &str = "
P1 eq-then-ne: x=[0..=1, 3..=4] y=[0..=1, 3..=4]
P2 ne-then-eq: x=[0..=1, 3..=4] y=[0..=1, 3..=4]
P3 le-ge-sum: x=[0..=1, 3..=4] y=[0..=1, 3..=4]
P4 hop3: x=[0..=4] y=[0..=4] z=[0..=4]
D1 x>=3||y>=3, x+y<=4: x=[0..=1, 3..=4] y=[0..=1, 3..=4]
B0 singleton-edge: x=[1..=4] y=[2..=4]
B1 singleton-edge: x=[0..=0, 2..=4] y=[2..=4]
B2 singleton-edge: x=[0..=4] y=[3..=4]
B3 singleton-edge: x=[0..=4] y=[2..=4]
B4 singleton-edge: x=[0..=4] y=[2..=4]
L1 leaf-minimum: a=[1..] x=[0..=4] y=[0..=4]
C1 certificate-exit-join: a=[..] x=[..=5, 10..=15, 20..=25, 30..] y=[..=-18, -13..=-8, -3..=2, 7..]
U-5,-3,false: a=[0..] x=[0..=4] y=[0..=1]
U-5,-3,true: a=[0..] x=[0..=4] y=[0..=1]
U-5,-2,false: a=[0..] x=[0..=4] y=[0..=1]
U-5,-2,true: a=[0..] x=[0..=4] y=[0..=1]
U-5,-1,false: a=[0..] x=[0..=4] y=[0..=1]
U-5,-1,true: a=[0..] x=[0..=4] y=[0..=1]
U-5,0,false: a=[0..] x=[0..=4] y=[0..=0]
U-5,0,true: a=[0..] x=[0..=4] y=[0..=0]
U-5,1,false: a=[1..] x=[1..=4] y=[0..=0]
U-5,1,true: a=[1..] x=[1..=4] y=[0..=0]
U-5,2,false: a=[2..] x=[2..=4] y=[0..=0]
U-5,2,true: a=[2..] x=[2..=4] y=[0..=0]
U-5,3,false: a=[3..] x=[3..=4] y=[0..=0]
U-5,3,true: a=[3..] x=[3..=4] y=[0..=0]
U-5,4,false: a=[4..] x=[4..=4] y=[0..=0]
U-5,4,true: a=[4..] x=[4..=4] y=[0..=0]
U-5,5,false: bottom
U-5,5,true: bottom
U-5,6,false: bottom
U-5,6,true: bottom
U-5,7,false: bottom
U-5,7,true: bottom
U-2,-3,false: a=[0..] x=[0..=4] y=[0..=3]
U-2,-3,true: a=[0..] x=[0..=4] y=[0..=3]
U-2,-2,false: a=[0..] x=[0..=4] y=[0..=3]
U-2,-2,true: a=[0..] x=[0..=4] y=[0..=3]
U-2,-1,false: a=[0..] x=[0..=4] y=[0..=2]
U-2,-1,true: a=[0..] x=[0..=4] y=[0..=2]
U-2,0,false: a=[0..] x=[0..=4] y=[0..=2]
U-2,0,true: a=[0..] x=[0..=4] y=[0..=2]
U-2,1,false: a=[1..] x=[1..=4] y=[0..=1]
U-2,1,true: a=[1..] x=[1..=4] y=[0..=1]
U-2,2,false: a=[2..] x=[2..=4] y=[0..=1]
U-2,2,true: a=[2..] x=[2..=4] y=[0..=1]
U-2,3,false: a=[3..] x=[3..=4] y=[0..=0]
U-2,3,true: a=[3..] x=[3..=4] y=[0..=0]
U-2,4,false: a=[4..] x=[4..=4] y=[0..=0]
U-2,4,true: a=[4..] x=[4..=4] y=[0..=0]
U-2,5,false: bottom
U-2,5,true: bottom
U-2,6,false: bottom
U-2,6,true: bottom
U-2,7,false: bottom
U-2,7,true: bottom
U-1,-3,false: a=[0..] x=[0..=4] y=[0..=4]
U-1,-3,true: a=[0..] x=[0..=4] y=[0..=4]
U-1,-2,false: a=[0..] x=[0..=4] y=[0..=4]
U-1,-2,true: a=[0..] x=[0..=4] y=[0..=4]
U-1,-1,false: a=[0..] x=[0..=4] y=[0..=4]
U-1,-1,true: a=[0..] x=[0..=4] y=[0..=4]
U-1,0,false: a=[0..] x=[0..=4] y=[0..=4]
U-1,0,true: a=[0..] x=[0..=4] y=[0..=4]
U-1,1,false: a=[1..] x=[1..=4] y=[0..=3]
U-1,1,true: a=[1..] x=[1..=4] y=[0..=3]
U-1,2,false: a=[2..] x=[2..=4] y=[0..=2]
U-1,2,true: a=[2..] x=[2..=4] y=[0..=2]
U-1,3,false: a=[3..] x=[3..=4] y=[0..=1]
U-1,3,true: a=[3..] x=[3..=4] y=[0..=1]
U-1,4,false: a=[4..] x=[4..=4] y=[0..=0]
U-1,4,true: a=[4..] x=[4..=4] y=[0..=0]
U-1,5,false: bottom
U-1,5,true: bottom
U-1,6,false: bottom
U-1,6,true: bottom
U-1,7,false: bottom
U-1,7,true: bottom
U1,-3,false: a=[0..] x=[0..=4] y=[0..=4]
U1,-3,true: a=[0..] x=[0..=4] y=[0..=4]
U1,-2,false: a=[0..] x=[0..=4] y=[0..=4]
U1,-2,true: a=[0..] x=[0..=4] y=[0..=4]
U1,-1,false: a=[0..] x=[0..=4] y=[0..=4]
U1,-1,true: a=[0..] x=[0..=4] y=[0..=4]
U1,0,false: a=[0..] x=[0..=4] y=[0..=4]
U1,0,true: a=[0..] x=[0..=4] y=[0..=4]
U1,1,false: a=[1..] x=[0..=4] y=[0..=4]
U1,1,true: a=[1..] x=[0..=4] y=[0..=4]
U1,2,false: a=[2..] x=[0..=4] y=[0..=4]
U1,2,true: a=[2..] x=[0..=4] y=[0..=4]
U1,3,false: a=[3..] x=[0..=4] y=[0..=4]
U1,3,true: a=[3..] x=[0..=4] y=[0..=4]
U1,4,false: a=[4..] x=[0..=4] y=[0..=4]
U1,4,true: a=[4..] x=[0..=4] y=[0..=4]
U1,5,false: a=[5..] x=[1..=4] y=[1..=4]
U1,5,true: a=[5..] x=[1..=4] y=[1..=4]
U1,6,false: a=[6..] x=[2..=4] y=[2..=4]
U1,6,true: a=[6..] x=[2..=4] y=[2..=4]
U1,7,false: a=[7..] x=[3..=4] y=[3..=4]
U1,7,true: a=[7..] x=[3..=4] y=[3..=4]
U2,-3,false: a=[0..] x=[0..=4] y=[0..=4]
U2,-3,true: a=[0..] x=[0..=4] y=[0..=4]
U2,-2,false: a=[0..] x=[0..=4] y=[0..=4]
U2,-2,true: a=[0..] x=[0..=4] y=[0..=4]
U2,-1,false: a=[0..] x=[0..=4] y=[0..=4]
U2,-1,true: a=[0..] x=[0..=4] y=[0..=4]
U2,0,false: a=[0..] x=[0..=4] y=[0..=4]
U2,0,true: a=[0..] x=[0..=4] y=[0..=4]
U2,1,false: a=[1..] x=[0..=4] y=[0..=4]
U2,1,true: a=[1..] x=[0..=4] y=[0..=4]
U2,2,false: a=[1..] x=[0..=4] y=[0..=4]
U2,2,true: a=[1..] x=[0..=4] y=[0..=4]
U2,3,false: a=[2..] x=[0..=4] y=[0..=4]
U2,3,true: a=[2..] x=[0..=4] y=[0..=4]
U2,4,false: a=[2..] x=[0..=4] y=[0..=4]
U2,4,true: a=[2..] x=[0..=4] y=[0..=4]
U2,5,false: a=[3..] x=[0..=4] y=[1..=4]
U2,5,true: a=[3..] x=[0..=4] y=[1..=4]
U2,6,false: a=[3..] x=[0..=4] y=[1..=4]
U2,6,true: a=[3..] x=[0..=4] y=[1..=4]
U2,7,false: a=[4..] x=[0..=4] y=[2..=4]
U2,7,true: a=[4..] x=[0..=4] y=[2..=4]
U5,-3,false: a=[0..] x=[0..=4] y=[0..=4]
U5,-3,true: a=[0..] x=[0..=4] y=[0..=4]
U5,-2,false: a=[0..] x=[0..=4] y=[0..=4]
U5,-2,true: a=[0..] x=[0..=4] y=[0..=4]
U5,-1,false: a=[0..] x=[0..=4] y=[0..=4]
U5,-1,true: a=[0..] x=[0..=4] y=[0..=4]
U5,0,false: a=[0..] x=[0..=4] y=[0..=4]
U5,0,true: a=[0..] x=[0..=4] y=[0..=4]
U5,1,false: a=[1..] x=[0..=4] y=[0..=4]
U5,1,true: a=[1..] x=[0..=4] y=[0..=4]
U5,2,false: a=[1..] x=[0..=4] y=[0..=4]
U5,2,true: a=[1..] x=[0..=4] y=[0..=4]
U5,3,false: a=[1..] x=[0..=4] y=[0..=4]
U5,3,true: a=[1..] x=[0..=4] y=[0..=4]
U5,4,false: a=[1..] x=[0..=4] y=[0..=4]
U5,4,true: a=[1..] x=[0..=4] y=[0..=4]
U5,5,false: a=[1..] x=[0..=4] y=[1..=4]
U5,5,true: a=[1..] x=[0..=4] y=[1..=4]
U5,6,false: a=[2..] x=[0..=4] y=[1..=4]
U5,6,true: a=[2..] x=[0..=4] y=[1..=4]
U5,7,false: a=[2..] x=[0..=4] y=[1..=4]
U5,7,true: a=[2..] x=[0..=4] y=[1..=4]
G1 shadow, base after part: x=[1..=4] y=[1..=2]
G2 hole in eliminated y: x=[0..=1, 3..=4] y=[0..=1, 3..=4]
G3 two lower rows: x=[0..=3] y=[0..=4] z=[0..=4]
G4 shadow, woken by x <= 4: x=[1..=4] y=[1..=2]
G5 x <= 2y <= x + 1: x=[0..=4] y=[0..=2]
E1 G5 then y >= 1: x=[1..=5] y=[1..=3]
A26 audit seed 26 steps 0-4: a=[-8..=5] x=[-8..=3] y=[-8..=5] z=[-4..=8]
C1 x = 2w, x = 2y + 1: bottom
C2 x = 2w, x = y + 1: x=[2..=2, 4..=4] y=[1..=3] w=[1..=2]
C3 x = 2w + 1, x = 2y: bottom
C4 x = 3w + 1, x >= y: x=[1..=7] y=[0..=3] w=[0..=2]
";
