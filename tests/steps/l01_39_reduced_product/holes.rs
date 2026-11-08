//! Known precision limits of holes in a tree of difference constraints (COMPLEXITY.md S25).
//! A value that the holes of two names leave out together, and neither hole alone, is kept
//! in the scope though no solution has it. The scope stays sound: it keeps every value that
//! some solution has.
//!
//! Each test writes its system as a Zed function `ok` whose tests all hold in one arm, in
//! three orders: one nested `if` a test, the bounds and holes first; the same with the
//! differences first; and all tests in one `&&`. The interpreter runs `ok` at every point of
//! the bounds, and the values of the points where it gives 1 are the exact answer.

use std::collections::BTreeSet;

use zed_kernel::{Evaluator, Shared, Term, Value, World, on_stack};
use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};
use zedc::store::product::Arm;

use super::arms_of;

/// A system: its names, each with its bounds and its holes, and its difference tests.
struct System {
    names: &'static [(&'static str, i64, i64, &'static [i64])],
    differences: &'static [&'static str],
}

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

    /// The arm of `src` where every test holds, and the values of each name within its
    /// bounds that the arm's scope keeps.
    fn kept(&self, src: &str, nested: bool) -> Vec<BTreeSet<i64>> {
        let (_, _, a) = arms_of(src);
        // A nested `if` a test gives the arms of the outer tests holding first, in order, the
        // last of them the innermost; one `&&` gives its true arm first.
        let depth = if nested {
            self.bounds().len() + self.differences.len()
        } else {
            1
        };
        let arm: &Arm = &a[depth - 1];
        assert!(arm.outcome, "{src}: arm {} is {}", depth - 1, arm.guard);
        assert!(!arm.scope.bottom, "{src}: {}", arm.scope);
        self.names
            .iter()
            .map(|&(n, lo, hi, _)| {
                let ints = arm.scope.get(n).ints().clone();
                (lo..=hi).filter(|&v| ints.contains(v)).collect()
            })
            .collect()
    }

    /// Checks, in each order, that the interpreter gives `exact` for the name at `i`, that
    /// the scope keeps every value of every name some solution has, and that it keeps
    /// `today` for the name at `i`.
    fn check(&self, i: usize, exact: &[i64], today: &[i64]) {
        let (exact, today): (BTreeSet<i64>, BTreeSet<i64>) = (
            exact.iter().copied().collect(),
            today.iter().copied().collect(),
        );
        for (order, src) in self.programs() {
            let solved = self.exact(&src);
            assert_eq!(solved[i], exact, "{order}: the exact answer of {src}");
            let kept = self.kept(&src, order != "one conjunction");
            for (k, (s, h)) in solved.iter().zip(&kept).enumerate() {
                assert!(
                    s.is_subset(h),
                    "{order}: unsound, `{}` drops {:?} of {src}",
                    self.names[k].0,
                    s.difference(h).collect::<Vec<_>>()
                );
            }
            assert_ne!(
                kept[i], exact,
                "{order}: the answer is exact, the limit is closed: {src}"
            );
            assert_eq!(kept[i], today, "{order}: {src}");
        }
    }
}

/// A known precision limit (COMPLEXITY.md S25): `a` in `{3, 4, 5}`, `b` in `{5, 7}`, `c` in
/// `{6, 8}`, `b - c <= 0`, `c - a <= 3`, `a - b <= -2`. The solutions are `(3, 5, 6)` and
/// `(5, 7, 8)`, so the exact answer is `a` in `{3, 5}`; the scope keeps `a` in `{3, 4, 5}` in
/// every order. At `a = 4`, `b >= 6` leaves `b = 7`, so `c >= 7` leaves `c = 8`, and
/// `c - a <= 3` fails. Without the hole of `b`, `(4, 6, 6)` is a solution, and without the
/// hole of `c`, `(4, 7, 7)`: only the two holes together leave out `a = 4`. Sound: it keeps
/// every value of every name some solution has. If this test fails because the answer is
/// exact, the limit is closed: assert the exact answer and remove the sentence in S25.
#[test]
fn two_holes_that_together_leave_out_a_middle_value_are_a_known_precision_limit() {
    System {
        names: &[("a", 3, 5, &[]), ("b", 5, 7, &[6]), ("c", 6, 8, &[7])],
        differences: &["b - c <= 0", "c - a <= 3", "a - b <= -2"],
    }
    .check(0, &[3, 5], &[3, 4, 5]);
}

/// A known precision limit (COMPLEXITY.md S25): `x`, `y`, `z` in `0..=6`,
/// `z <= y <= x <= z + 1`, `x != 5`, `y != 4`. At `z = 4`, `y` is 4 or 5 and `x` is 4 or 5;
/// `y != 4` leaves `y = 5`, so `x = 5`, which `x != 5` leaves out. Every other `z` has a
/// solution (as `(x, y, z)`: `(z, z, z)` for `z` up to 3, `(6, 5, 5)` and `(6, 6, 6)`), so the
/// exact answer is `z` in `{0, 1, 2, 3, 5, 6}`; the scope keeps `z` in `0..=6` in every
/// order. Without the hole of `x`, `(5, 5, 4)` is a solution, and without the hole of `y`,
/// `(4, 4, 4)`: only the two holes together leave out `z = 4`. Sound: it keeps every value of
/// every name some solution has. If this test fails because the answer is exact, the limit
/// is closed: assert the exact answer and remove the sentence in S25.
#[test]
fn two_holes_on_a_cycle_that_together_leave_out_a_value_are_a_known_precision_limit() {
    System {
        names: &[("x", 0, 6, &[5]), ("y", 0, 6, &[4]), ("z", 0, 6, &[])],
        differences: &["z <= y", "y <= x", "x <= z + 1"],
    }
    .check(2, &[0, 1, 2, 3, 5, 6], &[0, 1, 2, 3, 4, 5, 6]);
}
