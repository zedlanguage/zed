//! Holes in the names of a tree of difference constraints (item ST-holes-moves, COMPLEXITY.md
//! S25). The ends of each name are exact in every order: its least and greatest values over
//! the solutions. A value between the ends that the holes of two names on a cycle leave out
//! together, and neither hole alone, is kept in the scope though no solution has it, a known
//! precision limit (item O4 of the cross-review xst). The scope stays sound: it keeps every
//! value that some solution has. A part that its constraints join in more than one cycle, with
//! holes in three of its names or more, is refused with a warning of its own.
//!
//! Each test writes its system as a Zed function `ok` whose tests all hold in one arm, in
//! three orders: one nested `if` a test, the bounds and holes first; the same with the
//! differences first; and all tests in one `&&`. The interpreter runs `ok` at every point of
//! the bounds, and the values of the points where it gives 1 are the exact answer.

use std::collections::BTreeSet;
use std::sync::Arc;

use zed_kernel::{Evaluator, Prim, Shared, Term, Value, World, on_stack};
use zed_tests::scaling;
use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};
use zedc::store::cell::Premises;
use zedc::store::product::{Arm, Scope};

use super::{arms_of, ints};

/// A system: its names, each with its bounds and its holes, and its difference tests.
struct System {
    names: &'static [(&'static str, i64, i64, &'static [i64])],
    differences: &'static [&'static str],
}

/// One order's name, its program, and each name's exact values and those kept.
type Ends = (&'static str, String, Vec<BTreeSet<i64>>, Vec<BTreeSet<i64>>);

impl System {
    /// The tests of the bounds and holes, as Zed source.
    fn bounds(&self) -> Vec<String> {
        self.names
            .iter()
            .flat_map(|&(n, lo, hi, holes)| {
                [format!("{n} >= {lo}"), format!("{n} <= {hi}")]
                    .into_iter()
                    .chain(holes.iter().map(move |h| format!("{n} != {h}")))
            })
            .collect()
    }

    /// The function `ok` that gives 1 where `tests` all hold and 0 elsewhere, in one nested
    /// `if` a test, or in one `&&`.
    fn program(&self, tests: &[String], nested: bool) -> String {
        let ps: Vec<String> = self
            .names
            .iter()
            .map(|(n, ..)| format!("positional {n}"))
            .collect();
        let body = if nested {
            tests.iter().rev().fold("1".to_string(), |b, t| {
                format!("if {t} {{ {b} }} else {{ 0 }}")
            })
        } else {
            format!("if {} {{ 1 }} else {{ 0 }}", tests.join(" && "))
        };
        format!("ok({}) = {body};", ps.join(", "))
    }

    /// The programs in the three orders, each with its name.
    fn programs(&self) -> Vec<(&'static str, String)> {
        let b = self.bounds();
        let d: Vec<String> = self.differences.iter().map(|t| t.to_string()).collect();
        let first = |x: &[String], y: &[String]| -> Vec<String> { [x, y].concat() };
        vec![
            ("bounds first", self.program(&first(&b, &d), true)),
            ("differences first", self.program(&first(&d, &b), true)),
            ("one conjunction", self.program(&first(&b, &d), false)),
        ]
    }

    /// The values of each name over the points where `ok` of `src` gives 1, by the
    /// interpreter, at every point of the bounds.
    fn exact(&self, src: &str) -> Vec<BTreeSet<i64>> {
        let ok = elab(src)
            .unwrap_or_else(|e| panic!("{src}: {e:?}"))
            .get("ok")
            .expect("a definition `ok`");
        let k = self.names.len();
        let mut out = vec![BTreeSet::new(); k];
        let mut point: Vec<i64> = self.names.iter().map(|&(_, lo, ..)| lo).collect();
        loop {
            let args = point.iter().map(|&v| Term::Lit(Value::Int(v))).collect();
            let call = with_prelude(Term::App(Shared::new(ok.clone()), args));
            let v = on_stack(|| Evaluator::new(World::new()).run(&call))
                .unwrap_or_else(|e| panic!("{src}: ok{point:?} failed: {e:?}"));
            if v == Value::Int(1) {
                for (o, &x) in out.iter_mut().zip(&point) {
                    o.insert(x);
                }
            } else {
                assert_eq!(v, Value::Int(0), "{src}: ok{point:?}");
            }
            // The next point, the first name counting fastest.
            let mut i = 0;
            while i < k && point[i] == self.names[i].2 {
                point[i] = self.names[i].1;
                i += 1;
            }
            if i == k {
                return out;
            }
            point[i] += 1;
        }
    }

    /// The arm of `src` where every test holds.
    fn arm(&self, src: &str, nested: bool) -> Arm {
        let (_, _, mut a) = arms_of(src);
        // A nested `if` a test gives the arms of the outer tests holding first, in order, the
        // last of them the innermost; one `&&` gives its true arm first.
        let depth = if nested {
            self.bounds().len() + self.differences.len()
        } else {
            1
        };
        let arm = a.swap_remove(depth - 1);
        assert!(arm.outcome, "{src}: arm {} is {}", depth - 1, arm.guard);
        arm
    }

    /// The values of each name within its bounds that the arm of `src` where every test holds
    /// keeps.
    fn kept(&self, src: &str, nested: bool) -> Vec<BTreeSet<i64>> {
        let arm = self.arm(src, nested);
        assert!(!arm.scope.bottom, "{src}: {}", arm.scope);
        self.names
            .iter()
            .map(|&(n, lo, hi, _)| {
                let ints = arm.scope.get(n).ints().clone();
                (lo..=hi).filter(|&v| ints.contains(v)).collect()
            })
            .collect()
    }

    /// Checks, in each order, that the scope keeps every value of every name some solution
    /// has, and the least and greatest of them; gives the exact values and those kept, by
    /// order.
    fn ends(&self) -> Vec<Ends> {
        let mut out = Vec::new();
        for (order, src) in self.programs() {
            let solved = self.exact(&src);
            let kept = self.kept(&src, order != "one conjunction");
            for (k, (s, h)) in solved.iter().zip(&kept).enumerate() {
                let n = self.names[k].0;
                assert!(
                    s.is_subset(h),
                    "{order}: unsound, `{n}` drops {:?} of {src}",
                    s.difference(h).collect::<Vec<_>>()
                );
                assert_eq!(
                    (h.first(), h.last()),
                    (s.first(), s.last()),
                    "{order}: the ends of `{n}` in {src}"
                );
            }
            out.push((order, src, solved, kept));
        }
        out
    }

    /// Checks, in each order, that the scope keeps exactly the values some solution has, of
    /// every name.
    fn check_exact(&self) {
        for (order, src, solved, kept) in self.ends() {
            assert_eq!(kept, solved, "{order}: {src}");
        }
    }

    /// Checks, in each order, that the ends are exact, that the interpreter gives `exact` for
    /// the name at `i`, and that the scope keeps `today` for it, a value between its ends that
    /// no solution has.
    fn check(&self, i: usize, exact: &[i64], today: &[i64]) {
        let (exact, today): (BTreeSet<i64>, BTreeSet<i64>) = (
            exact.iter().copied().collect(),
            today.iter().copied().collect(),
        );
        for (order, src, solved, kept) in self.ends() {
            assert_eq!(solved[i], exact, "{order}: the exact answer of {src}");
            assert_ne!(
                kept[i], exact,
                "{order}: the answer is exact, the limit is closed: {src}"
            );
            assert_eq!(kept[i], today, "{order}: {src}");
        }
    }

    /// Checks, in each order, that no point holds every test and that the arm where they all
    /// hold is one no state reaches.
    fn check_empty(&self) {
        for (order, src) in self.programs() {
            assert!(
                self.exact(&src).iter().all(BTreeSet::is_empty),
                "{order}: a solution of {src}"
            );
            let arm = self.arm(&src, order != "one conjunction");
            assert!(arm.scope.bottom, "{order}: {src}: {}", arm.scope);
        }
    }

    /// The warnings of the arm where every test holds, in each order.
    fn warnings(&self) -> Vec<(&'static str, Vec<String>)> {
        self.programs()
            .into_iter()
            .map(|(order, src)| {
                let arm = self.arm(&src, order != "one conjunction");
                let ws = arm.scope.warnings().iter().map(|w| w.to_string()).collect();
                (order, ws)
            })
            .collect()
    }
}

/// A known precision limit (item O4 of the cross-review xst, COMPLEXITY.md S25): `a` in
/// `{3, 4, 5}`, `b` in `{5, 7}`, `c` in `{6, 8}`, `b - c <= 0`, `c - a <= 3`, `a - b <= -2`.
/// The solutions are `(3, 5, 6)` and `(5, 7, 8)`, so the exact answer is `a` in `{3, 5}`; the
/// scope keeps `a` in `{3, 4, 5}` in every order, with each name's ends exact. At `a = 4`,
/// `b >= 6` leaves `b = 7`, so `c >= 7` leaves `c = 8`, and `c - a <= 3` fails. Without the
/// hole of `b`, `(4, 6, 6)` is a solution, and without the hole of `c`, `(4, 7, 7)`: only the
/// two holes together leave out `a = 4`. Sound: it keeps every value of every name some
/// solution has. If this test fails because the answer is exact, the limit is closed: assert
/// the exact answer and remove the sentence in S25.
#[test]
fn two_holes_that_together_leave_out_a_middle_value_are_a_known_precision_limit() {
    System {
        names: &[("a", 3, 5, &[]), ("b", 5, 7, &[6]), ("c", 6, 8, &[7])],
        differences: &["b - c <= 0", "c - a <= 3", "a - b <= -2"],
    }
    .check(0, &[3, 5], &[3, 4, 5]);
}

/// A known precision limit (item O4 of the cross-review xst, COMPLEXITY.md S25): `x`, `y`,
/// `z` in `0..=6`, `z <= y <= x <= z + 1`, `x != 5`, `y != 4`. At `z = 4`, `y` is 4 or 5 and
/// `x` is 4 or 5; `y != 4` leaves `y = 5`, so `x = 5`, which `x != 5` leaves out. Every other
/// `z` has a solution (as `(x, y, z)`: `(z, z, z)` for `z` up to 3, `(6, 5, 5)` and
/// `(6, 6, 6)`), so the exact answer is `z` in `{0, 1, 2, 3, 5, 6}`; the scope keeps `z` in
/// `0..=6` in every order, with each name's ends exact. Without the hole of `x`, `(5, 5, 4)`
/// is a solution, and without the hole of `y`, `(4, 4, 4)`: only the two holes together leave
/// out `z = 4`. Sound: it keeps every value of every name some solution has. If this test
/// fails because the answer is exact, the limit is closed: assert the exact answer and remove
/// the sentence in S25.
#[test]
fn two_holes_on_a_cycle_that_together_leave_out_a_value_are_a_known_precision_limit() {
    System {
        names: &[("x", 0, 6, &[5]), ("y", 0, 6, &[4]), ("z", 0, 6, &[])],
        differences: &["z <= y", "y <= x", "x <= z + 1"],
    }
    .check(2, &[0, 1, 2, 3, 5, 6], &[0, 1, 2, 3, 4, 5, 6]);
}

/// A slot booking: `a` in `{4, 5}`, `b` in `{4, 6}`, `c` in `{2, 4}`, `c <= b - 2`,
/// `a <= c + 2`, `b <= a`. The one solution is `(4, 4, 2)`: `b <= a <= 5` leaves `b = 4`,
/// so `c <= 2`, so `a <= 4`. Each name is one value in every order, which the holes of `b`
/// and `c` on the cycle give only together: shortest paths over the hulls keep `a` up to 5
/// (CE-A of the cross-review xst).
#[test]
fn two_holes_on_a_cycle_give_the_one_solution_in_every_order() {
    System {
        names: &[("a", 4, 5, &[]), ("b", 4, 6, &[5]), ("c", 2, 4, &[3])],
        differences: &["c - b <= -2", "a - c <= 2", "b - a <= 0"],
    }
    .check_exact();
}

/// Three names with holes on one cycle, `x <= y <= z <= x + 1`, `x` in `{0, 3}`, `y` in
/// `{1, 4}`, `z` in `{0, 2}`: no point holds them all, though each name's hull meets the
/// others' (`x = y = z = 1` without the holes), and the scope is one no state reaches in
/// every order.
#[test]
fn three_holes_on_a_cycle_that_leave_no_point_empty_the_scope() {
    System {
        names: &[
            ("x", 0, 4, &[1, 2, 4]),
            ("y", 0, 4, &[0, 2, 3]),
            ("z", 0, 4, &[1, 3, 4]),
        ],
        differences: &["x <= y", "y <= z", "z <= x + 1"],
    }
    .check_empty();
}

/// A staircase of four names, each with a hole one step lower than the last, on one cycle
/// of equal values, `x0 >= x1 >= x2 >= x3 >= x0`, in `0..=8`: equal values leave out every
/// hole of every name, so each name is `0..=4`, in every order.
#[test]
fn a_staircase_of_holes_on_one_cycle_is_exact() {
    System {
        names: &[
            ("x0", 0, 8, &[8]),
            ("x1", 0, 8, &[7]),
            ("x2", 0, 8, &[6]),
            ("x3", 0, 8, &[5]),
        ],
        differences: &["x0 >= x1", "x1 >= x2", "x2 >= x3", "x3 >= x0"],
    }
    .check_exact();
}

/// Holes in three names of a part that the constraints join both ways in two cycles,
/// `z <= y <= x <= z + 1` and `z <= x <= y + 1`, each test a nested `if`: no method near
/// linear in the names is known for the ends, so the part is projected one block at a time
/// and a warning of its own says so. The warning depends on the constraints and on which
/// names have holes alone: other holes in the same names give the same warning. Each depth
/// where the tests so far already join the names in two cycles warns, each warning naming its
/// own constraints. In one `&&` the hole tests stay in the relation as conjuncts that are
/// not differences or bounds, so the tree is projected block by block, as before this item,
/// with no warning. The scope stays sound in every order.
#[test]
fn holes_on_three_names_of_two_cycles_are_refused() {
    const DIFFERENCES: &[&str] = &["z <= y", "y <= x", "x <= z + 1", "z <= x", "x <= y + 1"];
    let a = System {
        names: &[("x", 0, 6, &[5]), ("y", 0, 6, &[4]), ("z", 0, 6, &[3])],
        differences: DIFFERENCES,
    };
    let b = System {
        names: &[("x", 0, 6, &[2]), ("y", 0, 6, &[1, 3]), ("z", 0, 6, &[4])],
        differences: DIFFERENCES,
    };
    let head = "warning: the ends of names with holes are not found exactly\n  \
        [1] the constraints `";
    let tail = "` hold in the scope\n  \
        [2] they join their 3 names both ways in more than one cycle, and 3 of them have \
        holes: `x`, `y`, `z`; the ends of such names are found exactly when at most two of \
        them have holes\n  \
        [3] the names of the constraints are narrowed one block at a time, and their ends may \
        be wider than the constraints make them";
    let all = format!("{head}x <= y + 1 && x <= z + 1 && x >= y && x >= z && y >= z{tail}");
    for s in [a, b] {
        for (order, ws) in s.warnings() {
            let found: Vec<&String> = ws
                .iter()
                .filter(|w| w.contains("the ends of names with holes"))
                .collect();
            if order == "one conjunction" {
                assert!(found.is_empty(), "{order}: {found:?}");
                continue;
            }
            assert!(found.contains(&&all), "{order}: {ws:?}");
            for w in found {
                assert!(w.starts_with(head) && w.ends_with(tail), "{order}: {w}");
            }
        }
        for (order, src) in s.programs() {
            let solved = s.exact(&src);
            let kept = s.kept(&src, order != "one conjunction");
            for (x, y) in solved.iter().zip(&kept) {
                assert!(x.is_subset(y), "{order}: unsound in {src}");
            }
            if order == "one conjunction" {
                for (x, y) in solved.iter().zip(&kept) {
                    assert_eq!((x.first(), x.last()), (y.first(), y.last()), "{src}");
                }
            }
        }
    }
}

fn var(x: &str) -> Term {
    Term::Var(x.into())
}

fn int(v: i64) -> Term {
    Term::Lit(Value::Int(v))
}

fn prim(p: Prim, a: Term, b: Term) -> Term {
    Term::Prim(p, vec![a, b])
}

/// The conjunction of `ts`, balanced, so its depth is the log of their number.
fn all(ts: &[Term]) -> Term {
    match ts {
        [t] => t.clone(),
        _ => {
            let (a, b) = ts.split_at(ts.len() / 2);
            prim(Prim::And, all(a), all(b))
        }
    }
}

fn x(i: usize) -> String {
    format!("x{i}")
}

/// A ring of `n` names `x0` to `x{n - 1}`, each within `0..=r` and without the values
/// `holes(i)` gives for it, as a scope, and the differences `x{i + 1} <= x{i}` and
/// `x0 <= x{n - 1} + lap` as one conjunction. Each name's bounds and holes are one test of
/// that name alone, `x0 >= 0 && x0 <= r && x0 != 1 && …`, whose preimage is exact, so its
/// product holds them and the relation does not. (In one test of two names or more, the
/// relation keeps a hole test as a conjunct that is not a difference or a bound, and the tree
/// is projected block by block, as before item ST-holes-moves.)
fn ring(n: usize, r: i64, lap: i64, holes: impl Fn(usize) -> Vec<i64>) -> (Scope, Term) {
    let names: Vec<Arc<str>> = (0..n).map(|i| x(i).into()).collect();
    let p = Premises::new();
    let mut scope = ints(&names);
    for i in 0..n {
        let mut tests = vec![
            prim(Prim::Ge, var(&x(i)), int(0)),
            prim(Prim::Le, var(&x(i)), int(r)),
        ];
        tests.extend(
            holes(i)
                .into_iter()
                .map(|h| prim(Prim::Ne, var(&x(i)), int(h))),
        );
        scope = scope.assume(&all(&tests), true, &p);
    }
    let mut differences: Vec<Term> = (0..n - 1)
        .map(|i| prim(Prim::Le, var(&x(i + 1)), var(&x(i))))
        .collect();
    let closing = prim(Prim::Add, var(&x(n - 1)), int(lap));
    differences.push(prim(Prim::Le, var(&x(0)), closing));
    (scope, all(&differences))
}

/// The laps of [`scaling_of_one_cycle_of_holes_is_near_linear`]: `x0` a multiple of 3 and
/// `x{n / 2}` 0 or 1 more than one, within `0..=r`, on a ring of lap 1.
fn laps(n: usize, r: i64, more: impl Fn(usize) -> Vec<i64>) -> (Scope, Term) {
    ring(n, r, 1, |i| {
        let mut h = more(i);
        if i == 0 {
            h.extend((0..=r).filter(|v| v % 3 != 0));
        } else if i == n / 2 {
            h.extend((1..=r).filter(|v| v % 3 != 1));
        }
        h
    })
}

/// The values each name of `s` keeps, as the scope prints them.
fn printed(s: &Scope, n: usize) -> Vec<String> {
    (0..n).map(|i| s.get(&x(i)).ints().to_string()).collect()
}

#[test]
fn scaling_of_one_cycle_of_holes_is_near_linear() {
    // Three rings of `n` names, each with its bounds and holes in the scope, narrowed by its
    // `n` differences in one conjunction.
    //
    // Laps: `x0` a multiple of 3 and `x{n / 2}` 0 or 1 more than one, within `0..=6n`, and
    // `x0 >= x1 >= … >= x{n - 1} >= x0 - 1`: `x{n / 2}` is `x0` or `x0 - 1`, which only 0 is
    // both, so every name is 0. Narrowing the names in turn takes one lap of the ring for each
    // multiple of 3 it leaves out, `2n` laps of `n` names.
    //
    // Staircase: within `0..=2n`, `x{i}` without `2n - i`, all equal: every name is in `0..=n`,
    // and narrowing in turn takes a lap for each hole.
    //
    // Mixed: the laps within `0..=3n`, and `x{i}` without `3n - i` too.
    //
    // The ends solve each ring once, by composing the maps of its names around it (COMPLEXITY.md
    // S25), so each is near linear in `n`. The scopes and conjunctions are built before the
    // timing.
    let p = Premises::new();
    type Ring = fn(usize) -> (Scope, Term);
    type Family = (&'static str, Ring, fn(usize) -> Vec<String>);
    let families: [Family; 3] = [
        (
            "a ring of n names, two with holes every third value, in 0..=6n",
            |n| laps(n, 6 * n as i64, |_| Vec::new()),
            |n| vec!["[0..=0]".to_string(); n],
        ),
        (
            "a staircase of n names on one cycle, each with one hole, in 0..=2n",
            |n| ring(n, 2 * n as i64, 0, |i| vec![2 * n as i64 - i as i64]),
            |n| vec![format!("[0..={n}]"); n],
        ),
        (
            "a ring of n names, two with holes every third value and each with one hole, in 0..=3n",
            |n| laps(n, 3 * n as i64, |i| vec![3 * n as i64 - i as i64]),
            |n| vec!["[0..=0]".to_string(); n],
        ),
    ];
    for (what, family, expected) in families {
        for n in [4, 9, 16] {
            let (s, d) = family(n);
            assert_eq!(
                printed(&s.assume(&d, true, &p), n),
                expected(n),
                "{what}, n = {n}"
            );
        }
        let built = scaling::inputs(64, family);
        scaling::check_order(what, 64, 1, |n| {
            let (s, d) = &built[&n];
            assert!(!s.assume(d, true, &p).bottom);
        });
    }
}
