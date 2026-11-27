//! The text of a term whose parts are shared (STAGE-print). A part held in two or more places
//! is written once, `partN = …;`, in a block around the nearest node every path to it passes
//! through, and each place writes `partN`. A part that reads a name bound in more than one
//! place reads it from one value, the env, a balanced tree of pairs with a slot for each such
//! name: `partN = envM -> …;`, each place writing `partN(envK)`, the env in scope there.
//!
//! `print::pretty_in` and `print::written` are the printers for a user: their text is a
//! program, no label in it, that reads back to a term with the same value. `Display`, `Debug`
//! and `print::pretty` are for debugging: they have no scope, and write such a part once with a
//! label, `#1=…` at its first place and `#1#` at the others.
//!
//! The text of `d` nested `if`s whose two arms are one part was `2^d` long; now it grows with
//! `d`. The text of `k` names each bound in two places, read by a part held in `m` places, was
//! `m k` long when each place passed every name (the attempt 8e3e01445); now it grows with
//! `m log k + k`. A short part is written in place as before, and a term with no shared part
//! is written as before.

use zed_kernel::print::{pretty_in, written};
use zed_kernel::term::build::{lit, var};
use zed_kernel::text::ident::written_name;
use zed_kernel::{Evaluator, Pattern, Prim, Shared, Term, Value, World};
use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};

fn prim(p: Prim, args: Vec<Term>) -> Term {
    Term::Prim(p, args)
}

/// `n -> td`: `t0 = n + 100`, `tj = if n >= j { t(j-1) } else { t(j-1) }`, the two arms of each
/// `if` one part when `shared`, else two copies (`2^d` places either way).
pub(super) fn arms(d: usize, shared: bool) -> Term {
    fn at(j: usize, shared: bool) -> Shared {
        if j == 0 {
            return Shared::new(prim(Prim::Add, vec![var("n"), lit(100i64)]));
        }
        let guard = Shared::new(prim(Prim::Ge, vec![var("n"), lit(j as i64)]));
        let below = at(j - 1, shared);
        let other = match shared {
            true => below.clone(),
            false => at(j - 1, false),
        };
        Shared::new(Term::If(guard, below, other))
    }
    if shared {
        let t = (1..=d).fold(at(0, true), |below, j| {
            let guard = Shared::new(prim(Prim::Ge, vec![var("n"), lit(j as i64)]));
            Shared::new(Term::If(guard, below.clone(), below))
        });
        return Term::Lam(vec!["n".into()], t);
    }
    Term::Lam(vec!["n".into()], at(d, false))
}

/// `(y0, c) -> t0`: `tj = if c { y(j+1) = yj + 1; t(j+1) } else { y(j+1) = yj + 2; t(j+1) }`
/// and `td = yd`, the part below each level one node: it reads `yj`, which each of its places
/// binds anew.
pub(super) fn lets(d: usize) -> Term {
    let y = |j: usize| format!("y{j}");
    let t = (1..=d).rev().fold(Shared::new(var(&y(d))), |below, j| {
        let step = |k: i64| {
            let sum = Shared::new(prim(Prim::Add, vec![var(&y(j - 1)), lit(k)]));
            Shared::new(Term::Let(y(j).into(), sum, below.clone()))
        };
        Shared::new(Term::If(Shared::new(var("c")), step(1), step(2)))
    });
    Term::Lam(vec!["y0".into(), "c".into()], t)
}

/// `c -> if c { x1 = 1; …; xk = 1; B } else { x1 = 2; …; xk = 2; B }`, the two arms holding one
/// node `B = { z1 = { q = Q; (q, 1) }; …; zm = { q = Q; (q, m) }; (z1, …, zm) }` and the `m`
/// blocks one node `Q = x1 + … + xk`: `Q` reads `k` names each bound in two places, and is
/// held in `m` places, each under a binder of `q`, which is bound in `m` places too.
pub(super) fn wide(k: usize, m: usize) -> Term {
    let x = |i: usize| format!("x{i}");
    let q = (2..=k).fold(Term::Var(x(1).into()), |s, i| {
        prim(Prim::Add, vec![s, Term::Var(x(i).into())])
    });
    let q = Shared::new(q);
    let z = |i: usize| format!("z{i}");
    let tuple = Shared::new(prim(
        Prim::Tuple,
        (1..=m).map(|i| Term::Var(z(i).into())).collect(),
    ));
    let b = (1..=m).rev().fold(tuple, |body, i| {
        let pair = prim(Prim::Tuple, vec![var("q"), lit(i as i64)]);
        let block = Term::Let("q".into(), q.clone(), Shared::new(pair));
        Shared::new(Term::Let(z(i).into(), Shared::new(block), body))
    });
    let arm = |v: i64| {
        (1..=k).rev().fold(b.clone(), |body, i| {
            Shared::new(Term::Let(x(i).into(), Shared::new(lit(v)), body))
        })
    };
    Term::Lam(
        vec!["c".into()],
        Shared::new(Term::If(Shared::new(var("c")), arm(1), arm(2))),
    )
}

/// `x1 + … + xk`, one node.
fn sum_of_xs(k: usize) -> Shared {
    let x = |i: usize| var(&format!("x{i}"));
    Shared::new((2..=k).fold(x(1), |s, i| prim(Prim::Add, vec![s, x(i)])))
}

/// `c -> { x1 = 0; …; xk = 0; body }`, so that a part under `body` reading any `xj` reads a
/// name bound at each of its places.
fn under_zeros(k: usize, body: Shared) -> Term {
    let t = (1..=k).rev().fold(body, |body, j| {
        Shared::new(Term::Let(
            format!("x{j}").into(),
            Shared::new(lit(0i64)),
            body,
        ))
    });
    Term::Lam(vec!["c".into()], t)
}

/// `c -> { x1 = 0; …; xk = 0; T1 }`: `Tj = { xj = j; (T(j+1), { xj = j + 100; P }) }` for
/// `j < k`, `Tk = { xk = k; P }`, and `P = x1 + … + xk` one node: each `xj` is bound in three
/// places, and the part `P` is held under each `Tj`. The first item of each pair is built before
/// the second, so the env of `xj` has one env set from it when the text below it is built
/// (Claude C-1, round 2 of XR-lazy-and-kernel-batch-1, with the zeros added so that no name is
/// read free).
pub(super) fn chains(k: usize) -> Term {
    let p = sum_of_xs(k);
    let x = |i: usize| format!("x{i}");
    let inner = Term::Let(x(k).into(), Shared::new(lit(k as i64)), p.clone());
    let t = (1..k).rev().fold(inner, |below, j| {
        let second = Term::Let(x(j).into(), Shared::new(lit(j as i64 + 100)), p.clone());
        let pair = prim(Prim::Tuple, vec![below, second]);
        Term::Let(x(j).into(), Shared::new(lit(j as i64)), Shared::new(pair))
    });
    under_zeros(k, Shared::new(t))
}

/// `c -> { x1 = 0; …; xk = 0; T1 }`: `Tj = { xj = j; if c { T(j+1) } else { P } }` for
/// `j <= k`, `T(k+1) = P`, and `P = x1 + … + xk` one node: each `xj` but the first is read at a
/// place outside its inner binder, and the `then` arm is built before the `else` (Gemini C.1,
/// round 2 of XR-lazy-and-kernel-batch-1, with the zeros added so that no name is read free).
pub(super) fn spine(k: usize) -> Term {
    let p = sum_of_xs(k);
    let x = |i: usize| format!("x{i}");
    let t = (1..=k).rev().fold(p.clone(), |below, j| {
        let arms = Term::If(Shared::new(var("c")), below, p.clone());
        Shared::new(Term::Let(
            x(j).into(),
            Shared::new(lit(j as i64)),
            Shared::new(arms),
        ))
    });
    under_zeros(k, t)
}

/// `c -> if c { x = 1; P } else { x = 2; P }` and `P = { x = 3; (x, …, x) }` with `w` items: the
/// one name bound in more than one place is `x`, so the env is `x` itself, and `P` sets its slot
/// before any read of it, so the env passed to `P` is not read; it is named all the same, since
/// `_ ->` is not a lambda.
fn one_slot(w: usize) -> Term {
    let items = Shared::new(prim(Prim::Tuple, (0..w).map(|_| var("x")).collect()));
    let p = Shared::new(Term::Let("x".into(), Shared::new(lit(3i64)), items));
    let arm = |v: i64| Shared::new(Term::Let("x".into(), Shared::new(lit(v)), p.clone()));
    Term::Lam(
        vec!["c".into()],
        Shared::new(Term::If(Shared::new(var("c")), arm(1), arm(2))),
    )
}

/// No name of these terms is read free, so none resolves where they are written.
fn none(_: &str) -> bool {
    false
}

/// The text for a user, on one line, of a term no name of which is read free. (Broken into
/// lines, a term nested `d` deep is indented `O(d^2)` in all, a cost of the layout and not of
/// the parts, which the scaling tests do not measure.)
pub(super) fn shown(t: &Term) -> String {
    pretty_in(t, usize::MAX, &none)
}

/// `text` read back as the definition `x` of a unit.
fn read_back(text: &str) -> Term {
    let src = format!("x = {text};\n");
    let unit = elab(&src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    let x = unit.defs.iter().find(|d| d.name == "x").expect("`x`");
    (*x.term).clone()
}

/// `f` called on `args`, under the prelude.
fn call(f: &Term, args: &[Value]) -> Value {
    let args = args.iter().map(|v| Term::Lit(v.clone())).collect();
    let t = Term::App(Shared::new(f.clone()), args);
    Evaluator::new(World::new())
        .run(&with_prelude(t))
        .unwrap_or_else(|e| panic!("{f}: {e:?}"))
}

/// `text` is a program with no label, and reads back to a function that gives what `t` gives
/// on each of `inputs`.
fn reads_back_the_same(t: &Term, text: &str, inputs: &[Vec<Value>]) {
    assert!(!text.contains('#'), "{text}");
    let back = read_back(text);
    for args in inputs {
        assert_eq!(call(&back, args), call(t, args), "{text}");
    }
}

fn bools() -> Vec<Vec<Value>> {
    vec![vec![Value::Bool(true)], vec![Value::Bool(false)]]
}

#[test]
fn a_term_with_no_shared_part_and_a_short_shared_part_are_written_as_before() {
    for d in 0..=6 {
        let text = arms(d, false).to_string();
        assert!(!text.contains("part"), "{text}");
        assert_eq!(shown(&arms(d, false)), text);
    }
    assert_eq!(arms(0, false).to_string(), "n -> (n + 100)");
    // At d = 1 the part `n + 100` is shorter than a name for it would make the text.
    assert_eq!(
        arms(1, true).to_string(),
        "n -> if (n >= 1) { (n + 100) } else { (n + 100) }"
    );
    assert_eq!(arms(1, true).to_string(), arms(1, false).to_string());
    // At d = 2 the `if` below is named; it reads no name bound twice, so every printer writes
    // the same.
    let want = "n -> { part1 = if (n >= 1) { (n + 100) } else { (n + 100) }; \
                if (n >= 2) { part1 } else { part1 } }";
    assert_eq!(arms(2, true).to_string(), want);
    assert_eq!(shown(&arms(2, true)), want);
}

#[test]
fn nested_ifs_over_one_part_read_back_with_the_same_value() {
    let ns: Vec<Vec<Value>> = [-1i64, 0, 1, 3, 9].map(|n| vec![Value::Int(n)]).to_vec();
    for d in 0..=8 {
        let t = arms(d, true);
        reads_back_the_same(&t, &shown(&t), &ns);
    }
}

/// A part that reads a name bound at each of its places reads it from the env it is passed.
/// For a user the text is a program; `Display` labels the part instead.
#[test]
fn a_part_reading_a_name_bound_at_each_place_reads_it_from_the_env() {
    assert_eq!(
        shown(&lets(2)),
        "{ env2 = (0, 0); (y0, c) -> { part1 = env4 -> if c { { y2 = (env4[0] + 1); y2 } } \
         else { { y2 = (env4[0] + 2); y2 } }; if c { { y1 = (y0 + 1); env1 = (y1, env2[1]); \
         part1(env1) } } else { { y1 = (y0 + 2); env3 = (y1, env2[1]); part1(env3) } } } }"
    );
    let inputs: Vec<Vec<Value>> = [(0i64, true), (0, false), (5, true), (-3, false)]
        .map(|(x, c)| vec![Value::Int(x), Value::Bool(c)])
        .to_vec();
    for d in 0..=8 {
        let t = lets(d);
        reads_back_the_same(&t, &shown(&t), &inputs);
    }
    let text = lets(2).to_string();
    assert_eq!(text.matches("#1=").count(), 1, "{text}");
    assert_eq!(text.matches("#1#").count(), 1, "{text}");
    assert!(!text.contains("env"), "{text}");
}

/// With one name bound in more than one place the env is that name's value itself, and a part
/// that binds it before reading it does not read the env it is passed, and names it all the same.
#[test]
fn one_slot_is_the_value_itself_and_an_unread_env_is_named_all_the_same() {
    let t = one_slot(20);
    let text = shown(&t);
    assert!(
        text.contains("part1 = env") && !text.contains("_ ->"),
        "{text}"
    );
    assert!(!text.contains('['), "{text}");
    reads_back_the_same(&t, &text, &bools());
}

/// The wide family: a part reading `k` names bound twice, held in `m` places. For a user the
/// text and a message's text are programs that read back to the same value; for debugging the
/// parts are labeled, numbered in the order they are written.
#[test]
fn a_part_reading_many_names_bound_twice_reads_back_with_the_same_value() {
    for (k, m) in [(1, 1), (1, 4), (2, 3), (3, 4), (5, 2), (8, 8), (20, 30)] {
        let t = wide(k, m);
        reads_back_the_same(&t, &shown(&t), &bools());
        reads_back_the_same(&t, &pretty_in(&t, 40, &none), &bools());
        // A message writes each name as the program wrote it, here as it is.
        let message = written(&t, |x| x, &none);
        reads_back_the_same(&t, &message, &bools());
        let text = t.to_string();
        if text.contains('#') {
            assert!(text.contains("#1="), "{text}");
            assert!(
                text.find("#1=") < text.find("#2=").or(Some(usize::MAX)),
                "{text}"
            );
        }
    }
}

/// The two families whose updates walked a chain of envs once per binder (`chains` and
/// `spine`): the texts read back to the same value, and the text of 8 times the names is at
/// most 24 times as long (`bench::print` times them at 400 and 3200).
#[test]
fn a_chain_of_envs_passed_by_one_update_and_named_by_the_next_reads_back() {
    for make in [chains, spine] {
        for k in 1..=8 {
            let t = make(k);
            reads_back_the_same(&t, &shown(&t), &bools());
            reads_back_the_same(&t, &pretty_in(&t, 40, &none), &bools());
            reads_back_the_same(&t, &written(&t, |x| x, &none), &bools());
        }
        for k in [16, 50] {
            let (small, large) = (shown(&make(k)).len(), shown(&make(8 * k)).len());
            assert!(
                large <= 3 * 8 * small,
                "{small} at {k}, {large} at {}",
                8 * k
            );
        }
    }
}

/// The text of `t` in a message: each name as the program wrote it, `x` for the kernel's `x@1`
/// and `x@2` ([`written_name`]), as zedc-preimage prints a term.
fn message(t: &Term) -> String {
    written(t, written_name, &none)
}

fn let_(x: &str, e: Term, body: Term) -> Term {
    Term::Let(x.into(), Shared::new(e), Shared::new(body))
}

fn add(a: Term, b: Term) -> Term {
    prim(Prim::Add, vec![a, b])
}

fn sub(a: Term, b: Term) -> Term {
    prim(Prim::Sub, vec![a, b])
}

fn ten(a: Term) -> Term {
    prim(Prim::Mul, vec![a, lit(10i64)])
}

// Where a read of `x@1` in a message's text would name a binder of `x@2`, the binder takes a
// new name, `x2`, and the text reads back to the same value (round 2 of
// XR-lazy-and-kernel-batch-1: Codex D5 and C7, Gemini C.2). The values differ wherever a
// capture would change them.

/// Codex D5: the parameter read under a binder of another `x`; the kernel gives 9 for 9, the
/// text `x -> { { x = 5; x } }` gave 5.
#[test]
fn a_binder_written_as_a_parameter_read_under_it_takes_a_new_name() {
    let t = Term::Lam(
        vec!["x@1".into()],
        Shared::new(let_("x@2", lit(5i64), var("x@1"))),
    );
    let ints: Vec<Vec<Value>> = [9i64, -2].map(|n| vec![Value::Int(n)]).to_vec();
    assert_eq!(message(&t), "x -> { x2 = 5; x }");
    reads_back_the_same(&t, &message(&t), &ints);
}

/// Codex D5, "simultaneous differently bound parameter collisions": two parameters written
/// alike.
#[test]
fn a_second_parameter_written_as_the_first_takes_a_new_name() {
    let t = Term::Lam(
        vec!["x@1".into(), "x@2".into()],
        Shared::new(sub(var("x@1"), var("x@2"))),
    );
    let pairs: Vec<Vec<Value>> = [(9i64, 2i64), (-2, 7)]
        .map(|(a, b)| vec![Value::Int(a), Value::Int(b)])
        .to_vec();
    assert_eq!(message(&t), "(x, x2) -> x - x2");
    reads_back_the_same(&t, &message(&t), &pairs);
}

/// A control: a part reading `x@1`, bound in each arm and so read from the env, and `x@2`,
/// bound once above the `if`, where the part is defined; nothing is captured.
#[test]
fn a_part_reading_two_names_written_alike_from_its_env_and_its_scope_reads_back() {
    let items = (1..=4)
        .map(|i| {
            add(
                ten(var("x@1")),
                prim(Prim::Mul, vec![var("x@2"), lit(i as i64)]),
            )
        })
        .collect();
    let p = Shared::new(prim(Prim::Tuple, items));
    let arm = |a: i64| Shared::new(Term::Let("x@1".into(), Shared::new(lit(a)), p.clone()));
    let t = Term::Lam(
        vec!["c".into()],
        Shared::new(let_(
            "x@2",
            lit(2i64),
            Term::If(Shared::new(var("c")), arm(1), arm(5)),
        )),
    );
    let text = message(&t);
    assert!(text.contains("part1"), "{text}");
    reads_back_the_same(&t, &text, &bools());
}

/// Gemini C.2: inside a part, which reads `z` from its env, `x@1 = 1; x@2 = 2; … x@1 …`, `x@1`
/// bound outside the part too: the env at the binder of `x@1` in the part is set at that
/// binder, so the read of `x@1` is written as the name (`Builder::read`), under the binder of
/// `x@2`.
#[test]
fn a_read_of_an_env_set_at_its_binder_under_a_binder_written_alike_reads_back() {
    let items = (1..=4)
        .map(|i| {
            add(
                ten(var("x@1")),
                prim(Prim::Mul, vec![var("z"), lit(i as i64)]),
            )
        })
        .collect();
    let inner = Term::Let(
        "x@2".into(),
        Shared::new(lit(2i64)),
        Shared::new(prim(Prim::Tuple, items)),
    );
    let r = Shared::new(let_("x@1", lit(1i64), inner));
    let then = Term::Let("z".into(), Shared::new(lit(7i64)), r.clone());
    let y = Term::Let(
        "y".into(),
        Shared::new(add(var("x@1"), lit(1i64))),
        r.clone(),
    );
    let other = let_("z", lit(8i64), let_("x@1", lit(5i64), y));
    let t = Term::Lam(
        vec!["c".into()],
        Shared::new(Term::If(
            Shared::new(var("c")),
            Shared::new(then),
            Shared::new(other),
        )),
    );
    let text = message(&t);
    assert!(text.contains("part1") && text.contains("x2 = 2"), "{text}");
    reads_back_the_same(&t, &text, &bools());
}

/// Codex C7: an update setting the slots of `x@1` and `x@2` at once, under the binder of `x@2`,
/// with other values in each arm.
#[test]
fn an_update_setting_two_slots_written_alike_reads_back() {
    let items = vec![
        add(ten(var("x@1")), var("x@2")),
        add(var("x@1"), ten(var("x@2"))),
        sub(var("x@1"), var("x@2")),
    ];
    let p = Shared::new(prim(Prim::Tuple, items));
    let arm = |a: i64, b: i64| {
        let inner = Term::Let("x@2".into(), Shared::new(lit(b)), p.clone());
        Shared::new(let_("x@1", lit(a), inner))
    };
    let t = Term::Lam(
        vec!["c".into()],
        Shared::new(Term::If(Shared::new(var("c")), arm(1, 2), arm(3, 4))),
    );
    let text = message(&t);
    assert!(text.contains("part1") && text.contains("x2 = 2"), "{text}");
    reads_back_the_same(&t, &text, &bools());
}

fn pairs() -> Vec<Vec<Value>> {
    [(9i64, 2i64), (-2, 7)]
        .map(|(a, b)| vec![Value::Int(a), Value::Int(b)])
        .to_vec()
}

fn lam(xs: &[&str], body: Term) -> Term {
    Term::Lam(xs.iter().map(|&x| x.into()).collect(), Shared::new(body))
}

// Round 3 of XR-lazy-and-kernel-batch-1, part C.

/// Codex C2.1, Gemini C-1: two parameters of one lambda written alike, in either order, the body
/// reading one of them or neither. The text `(x, x) -> …` is refused, a name declared twice, so
/// the later of the two takes a new name whatever the body reads. Before the fix a body reading
/// the later parameter, or none, gave `(x, x) -> …`.
#[test]
fn a_parameter_written_as_an_earlier_one_takes_a_new_name_read_or_not() {
    let cases = [
        (lam(&["x@1", "x@2"], var("x@2")), "(x, x2) -> x2"),
        (lam(&["x@1", "x@2"], lit(1i64)), "(x, x2) -> 1"),
        (lam(&["x@2", "x@1"], var("x@1")), "(x, x2) -> x2"),
        (lam(&["x@2", "x@1"], var("x@2")), "(x, x2) -> x"),
        (lam(&["x@1", "x@2"], var("x@1")), "(x, x2) -> x"),
    ];
    for (t, want) in &cases {
        assert_eq!(message(t), *want);
        reads_back_the_same(t, want, &pairs());
    }
}

/// Codex C2.2: a free read of a kernel name whose binders take a new name keeps the name the
/// program wrote; only the binders and the reads they bind are respelled. Read back under a
/// parameter `x` given 47: before the fix the free read was written `x2` (or `x3`), which the
/// text does not bind.
#[test]
fn a_free_read_of_a_name_respelled_at_its_binders_keeps_its_written_name() {
    // `y -> (x@1 -> { x@2 = 5; x@1 })(y) + x@2`, the last `x@2` free.
    let f = lam(&["x@1"], let_("x@2", lit(5i64), var("x@1")));
    let call_f = Term::App(Shared::new(f), vec![var("y")]);
    let a = lam(&["y"], add(call_f, var("x@2")));
    // `x@1 -> x@2 + { x@2 = 5; x@1 + x@2 }`: the free read is under the binder of `x@1`, so
    // that binder is respelled and the free read is written `x`; the inner binder keeps `x`,
    // as no read of another `x` is under it once `x@1` is `x2`. The block is on the right: on
    // the left of `+` at the start of a body the printer writes it bare, and the parser ends
    // the body at its `}`.
    let b = lam(
        &["x@1"],
        add(
            var("x@2"),
            let_("x@2", lit(5i64), add(var("x@1"), var("x@2"))),
        ),
    );
    for (t, text, want) in [
        (&a, "y -> (x -> { x2 = 5; x })(y) + x", 9 + 47),
        (&b, "x2 -> x + { x = 5; x2 + x }", 47 + 9 + 5),
    ] {
        assert_eq!(message(t), text);
        let src = format!("g = x -> {text};\n");
        let unit = elab(&src).unwrap_or_else(|e| panic!("{src}: {e:?}"));
        let g = unit.defs.iter().find(|d| d.name == "g").expect("`g`");
        let given = Term::App(Shared::new((*g.term).clone()), vec![lit(47i64)]);
        assert_eq!(call(&given, &[Value::Int(9)]), Value::Int(want), "{text}");
    }
}

/// Gemini C-2: a binder written `x'` that takes a new name is numbered before the prime, `x2'`;
/// `x'2` is the name `x'` and the number 2. The text is not read back: the resolver of this step
/// refuses every primed name as a form of a later step (`Resolver::primed`, crates/zedc-resolve
/// resolve.rs), so no text with a primed binder reads back here.
#[test]
fn a_primed_binder_takes_a_new_name_with_the_number_before_the_prime() {
    let t = lam(&["x'@1"], let_("x'@2", lit(5i64), var("x'@1")));
    assert_eq!(message(&t), "x' -> { x2' = 5; x' }");
}

/// PRINT-block-left-operand-in-lambda-body: a lambda body or a match arm whose text starts with
/// `{` but is not a block, as a block first on the left of an operator or as a receiver, is in
/// parentheses. The grammar reads a `{` right after `->` as the body's block (sec:grammar,
/// `Lambda` and `Arm`: `Block | !'{' Expr`), so `x -> { y = 5; y } + x` ends the body at its
/// `}`, and the text is refused. Before the fix [`message`] wrote the block bare.
#[test]
fn a_body_starting_with_a_block_that_is_not_one_is_in_parentheses() {
    let block = || let_("y", lit(5i64), var("y"));
    let ints = [vec![Value::Int(9)], vec![Value::Int(-2)]];
    let cases = [
        (
            lam(&["x"], add(block(), var("x"))),
            "x -> ({ y = 5; y } + x)",
        ),
        (
            lam(
                &["x"],
                add(prim(Prim::Mul, vec![block(), var("x")]), lit(1i64)),
            ),
            "x -> ({ y = 5; y } * x + 1)",
        ),
        (
            lam(
                &["x"],
                prim(
                    Prim::TupleGet,
                    vec![
                        let_("y", prim(Prim::Tuple, vec![var("x"), lit(1i64)]), var("y")),
                        lit(0i64),
                    ],
                ),
            ),
            "x -> ({ y = (x, 1); y }[0])",
        ),
    ];
    for (t, want) in &cases {
        assert_eq!(message(t), *want);
        reads_back_the_same(t, want, &ints);
        // The other printers parenthesize every operator and every receiver that is not a
        // primary, so their text starts with `(` already.
        reads_back_the_same(t, &shown(t), &ints);
    }
    // A body that is a block stays one, with no parentheses.
    assert_eq!(message(&lam(&["x"], block())), "x -> { y = 5; y }");
    // A match arm: `match` is not read back at this step (see
    // `a_binding_reading_or_rebinding_a_name_a_pattern_or_fam_binds_reads_back`), so its text
    // is checked.
    let arms = vec![
        (Pattern::Lit(Value::Int(1)), add(block(), var("x"))),
        (Pattern::Wild, lit(0i64)),
    ];
    let t = lam(&["x"], Term::Match(Shared::new(var("x")), arms));
    assert_eq!(
        message(&t),
        "x -> match x { 1 -> ({ y = 5; y } + x), _ -> 0 }"
    );
}

/// Claude C-2 of round 3 (PRINT-port-names-taken): a binder that takes a new name does not take
/// the name of a port read or pushed under it. `port.read(p)` is a form of the printer only,
/// which no program writes, so the text is not read back; written `x2`, the binder would read
/// to a person as the port's argument.
#[test]
fn a_binder_taking_a_new_name_does_not_take_a_ports_name() {
    let read = lam(
        &["x@1"],
        let_("x@2", lit(5i64), add(Term::Read("x2".into()), var("x@1"))),
    );
    assert_eq!(message(&read), "x -> { x3 = 5; port.read(x2) + x }");
    let push = lam(
        &["x@1"],
        let_(
            "x@2",
            lit(5i64),
            Term::Push("x2".into(), Shared::new(var("x@1"))),
        ),
    );
    assert_eq!(message(&push), "x -> { x3 = 5; port.push(x2, x) }");
}

/// A part named in the text does not take a name the term writes: a parameter `part1` moves
/// the part to `part2`, and a name `env1` moves the env to `env2`.
#[test]
fn a_part_or_env_is_never_named_as_a_name_the_term_writes() {
    let t = arms(2, true);
    let Term::Lam(_, body) = &t else {
        unreachable!()
    };
    let t = Term::Lam(vec!["part1".into(), "n".into()], body.clone());
    for text in [t.to_string(), shown(&t)] {
        assert!(text.contains("part2 = "), "{text}");
        assert!(!text.contains("part1 = "), "{text}");
    }
    let t = lets(3);
    let Term::Lam(_, body) = &t else {
        unreachable!()
    };
    let t = Term::Lam(vec!["env1".into(), "c".into()], body.clone());
    let text = shown(&t);
    assert!(!text.contains("env1 ="), "{text}");
}

#[test]
fn the_text_does_not_depend_on_the_ids_of_parts() {
    for d in 0..=6 {
        // Two builds of one term, with other ids, and one print twice.
        let (a, b) = (arms(d, true), arms(d, true));
        assert_eq!(a.to_string(), b.to_string());
        assert_eq!(a.to_string(), a.to_string());
        assert_eq!(lets(d).to_string(), lets(d).to_string());
        assert_eq!(shown(&lets(d)), shown(&lets(d)));
        assert_eq!(shown(&wide(d, d + 1)), shown(&wide(d, d + 1)));
        assert_eq!(wide(d, d + 1).to_string(), wide(d, d + 1).to_string());
        assert_eq!(format!("{a:?}"), format!("{b:?}"));
    }
}

#[test]
fn debug_writes_a_part_held_twice_once() {
    let t = arms(2, true);
    let text = format!("{t:?}");
    assert_eq!(text.matches("#1=").count(), 1, "{text}");
    assert_eq!(text.matches("#1#").count(), 1, "{text}");
    assert_eq!(text.matches("100").count(), 1, "{text}");
    assert!(!format!("{:?}", arms(3, false)).contains("#1"));
}

/// The texts of 2 and 16 levels and of 8 times as many, by both printers: the longer is at most
/// 3 × 8 times as long (`bench::print` holds it at 400 and 3200 levels and times it). At one
/// level the names of the parts weigh most: `lets(8)` by `shown` is 32 times `lets(1)`.
#[test]
fn the_text_of_8_times_the_levels_is_at_most_24_times_as_long() {
    let printers: [fn(&Term) -> String; 2] = [shown, |t| t.to_string()];
    for d in [2, 16] {
        for print in printers {
            for make in [|d| arms(d, true), lets] {
                let (small, large) = (print(&make(d)).len(), print(&make(8 * d)).len());
                assert!(
                    large <= 3 * 8 * small,
                    "{small} at {d}, {large} at {}",
                    8 * d
                );
            }
        }
    }
}

/// `c -> { x0 = 0; …; x3 = 0; t }` with `t` drawn from `seed`: two pools of nodes, integers and
/// pairs of integers, built bottom-up, each node a read of an `xi`, a sum of an integer node
/// and a literal, a pair of two integer nodes, a `let` of an `xi` to an `xj` plus a literal
/// over a node, or an `if` on `c` or on `xi >= 1` over two nodes of one pool. Any later node
/// may hold a node, so parts are shared, and they read names their places bind differently,
/// in chains of `let`s of one or several names.
///
/// With `chains` (Claude C-3, Gemini C.3 of round 2), each `let` drawn is a chain of 2 to 6
/// `let`s over one node, so a chain often binds one name twice, and half the `if`s have one
/// node under both arms.
fn drawn(seed: u64, size: usize, chains: bool) -> Term {
    let mut s = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
    let mut next = |n: usize| {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        (s % n as u64) as usize
    };
    let x = |i: usize| format!("x{i}");
    // pools[0]: integers, pools[1]: pairs of integers.
    let mut pools: [Vec<Shared>; 2] = [(0..4).map(|i| Shared::new(var(&x(i)))).collect(), vec![]];
    let mut top = pools[0][0].clone();
    for _ in 0..size {
        let ints = &pools[0];
        let (a, b) = (
            ints[next(ints.len())].clone(),
            ints[next(ints.len())].clone(),
        );
        let kind = match pools[1].is_empty() {
            true => 0,
            false => next(2),
        };
        let pool = &pools[kind];
        let (p, q) = (
            pool[next(pool.len())].clone(),
            pool[next(pool.len())].clone(),
        );
        let k = next(5) as i64;
        let (kind, t) = match next(5) {
            0 => (0, prim(Prim::Add, vec![(*a).clone(), lit(k)])),
            1 => (1, prim(Prim::Tuple, vec![(*a).clone(), (*b).clone()])),
            2 => {
                // `xi = xj + k`, j = i included, over a body that may be a `let` itself: in a
                // program every binding of a block is in scope in the whole block, so the
                // printer must not write `xi = xi + k` reading the `xi` outside, nor a chain
                // whose binding reads a name a later `let` of the chain binds, in one block
                // (PRINT-let-reading-its-own-name).
                let n = match chains {
                    true => 2 + next(5),
                    false => 1,
                };
                let mut body = p;
                for _ in 1..n {
                    let e = prim(Prim::Add, vec![var(&x(next(4))), lit(next(5) as i64)]);
                    body = Shared::new(Term::Let(x(next(4)).into(), Shared::new(e), body));
                }
                let i = next(4);
                let e = prim(Prim::Add, vec![var(&x(next(4))), lit(k)]);
                (kind, Term::Let(x(i).into(), Shared::new(e), body))
            }
            3 if chains && next(2) == 0 => (kind, Term::If(Shared::new(var("c")), p.clone(), p)),
            3 => (kind, Term::If(Shared::new(var("c")), p, q)),
            _ => {
                let guard = prim(Prim::Ge, vec![var(&x(next(4))), lit(1i64)]);
                (kind, Term::If(Shared::new(guard), p, q))
            }
        };
        let t = Shared::new(t);
        pools[kind].push(t.clone());
        top = t;
    }
    let body = (0..4).rev().fold(top, |body, i| {
        Shared::new(Term::Let(x(i).into(), Shared::new(lit(0i64)), body))
    });
    Term::Lam(vec!["c".into()], body)
}

/// Each name `x` followed by digits written `x`, as a message writes `x@1` and `x@2`
/// ([`written_name`]): every name of a drawn term but `c` is one name in the text, so the
/// text reads back only where each binder that would capture a read takes a new name.
fn all_x(name: &str) -> &str {
    match name.strip_prefix('x') {
        Some(n) if !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()) => "x",
        _ => name,
    }
}

/// 400 drawn terms with shared parts, and 400 with chains of `let`s: the text for a user, on
/// one line and broken into lines, and a message's text, with each name as it is and with
/// the names written alike ([`all_x`], Gemini C.3 of round 2), each read back, give what the
/// term gives at `c` true and false.
#[test]
fn drawn_terms_with_shared_parts_read_back_with_the_same_value() {
    for chains in [false, true] {
        for seed in 0..400 {
            let t = drawn(seed, 4 + (seed as usize % 12), chains);
            reads_back_the_same(&t, &shown(&t), &bools());
            reads_back_the_same(&t, &pretty_in(&t, 40, &none), &bools());
            reads_back_the_same(&t, &written(&t, |x| x, &none), &bools());
            reads_back_the_same(&t, &written(&t, all_x, &none), &bools());
        }
    }
}

/// `c -> if g { x1 = a1; …; xk = ak; P } else { x1 = b1; …; xk = bk; P }` with `P` the tuple of
/// `10 xi + i`, every slot of a `k`-slot env read in each arm with values that differ by slot
/// and by arm, for `k` 1, 3 and 5 (Codex C4/C5: the item numbers of the env's pairs, one slot
/// the whole env), and `k` 0, a part reading no name bound twice.
#[test]
fn every_slot_of_an_env_of_1_3_or_5_slots_reads_back_in_both_arms() {
    for k in [0usize, 1, 3, 5] {
        let x = |i: usize| format!("x{i}");
        let items = (1..=k.max(1))
            .map(|i| match k {
                0 => add(ten(var("c0")), lit(i as i64)),
                _ => add(ten(var(&x(i))), lit(i as i64)),
            })
            .chain([lit(0i64), lit(1i64)])
            .collect();
        let p = Shared::new(prim(Prim::Tuple, items));
        let arm = |v: i64| {
            (1..=k).rev().fold(p.clone(), |body, i| {
                Shared::new(Term::Let(x(i).into(), Shared::new(lit(v + i as i64)), body))
            })
        };
        let body = Term::If(Shared::new(var("c")), arm(10), arm(20));
        let t = Term::Lam(vec!["c".into()], Shared::new(let_("c0", lit(3i64), body)));
        for text in [shown(&t), message(&t)] {
            reads_back_the_same(&t, &text, &bools());
        }
    }
}

/// Codex C1/C2: in one arm a chain `x = 1; y = 2; x = 3` above the part, so the update of the
/// env at the inner `x` passes the env of `y` and that of the outer `x`, and keeps the inner
/// `x`: the part reads 3, not 1. (Five items, so that the part is named rather than written in
/// place at each of its places.)
#[test]
fn a_chain_setting_one_slot_twice_keeps_the_inner_binder() {
    let items = (0..5)
        .map(|i| add(add(ten(var("x")), var("y")), lit(i as i64)))
        .collect();
    let p = Shared::new(prim(Prim::Tuple, items));
    let inner = Term::Let("x".into(), Shared::new(lit(3i64)), p.clone());
    let then = let_("x", lit(1i64), let_("y", lit(2i64), inner));
    let other = let_(
        "x",
        lit(4i64),
        Term::Let("y".into(), Shared::new(lit(5i64)), p.clone()),
    );
    let t = Term::Lam(
        vec!["c".into()],
        Shared::new(Term::If(
            Shared::new(var("c")),
            Shared::new(then),
            Shared::new(other),
        )),
    );
    for text in [shown(&t), message(&t)] {
        assert!(text.contains("part1"), "{text}");
        reads_back_the_same(&t, &text, &bools());
    }
}

/// Codex C3: a 5-slot env set in each arm, and in one arm two sibling places of the part each
/// rebinding another slot, so each sibling's update reads the pairs of the common env, named
/// once, defined before either sibling.
#[test]
fn sibling_updates_of_one_env_read_its_pairs_named_once() {
    let x = |i: usize| format!("x{i}");
    let items = (0..5)
        .map(|i| add(ten(var(&x(i))), lit(i as i64)))
        .collect();
    let p = Shared::new(prim(Prim::Tuple, items));
    let rebind =
        |i: usize, v: i64| Shared::new(Term::Let(x(i).into(), Shared::new(lit(v)), p.clone()));
    let guard = Shared::new(prim(Prim::Ge, vec![var("x0"), lit(1i64)]));
    let siblings = Shared::new(Term::If(guard, rebind(1, 7), rebind(3, 8)));
    let arm = |v: i64, body: Shared| {
        (0..5).rev().fold(body, |body, i| {
            Shared::new(Term::Let(x(i).into(), Shared::new(lit(v + i as i64)), body))
        })
    };
    let t = Term::Lam(
        vec!["c".into()],
        Shared::new(Term::If(
            Shared::new(var("c")),
            arm(10, siblings),
            arm(0, p.clone()),
        )),
    );
    for text in [shown(&t), message(&t)] {
        assert!(text.contains("part1"), "{text}");
        reads_back_the_same(&t, &text, &bools());
    }
}

/// A binding that reads a name its block binds: its own (`x = x + 1`, the `x` above), one a
/// later binding of the chain binds (`y = x + 1; x = 5`), or a parameter its lambda's body
/// binds again (`x -> { x = x + 1; x }`). Each text reads back to the term's value
/// (PRINT-let-reading-its-own-name).
#[test]
fn a_binding_reading_a_name_its_block_binds_reads_back_with_the_same_value() {
    let sh = |t: Term| Shared::new(t);
    let add = |a: Term, b: Term| prim(Prim::Add, vec![a, b]);
    let lam = |ps: &[&str], b: Term| Term::Lam(ps.iter().map(|p| (*p).into()).collect(), sh(b));
    let let_ = |x: &str, e: Term, b: Term| Term::Let(x.into(), sh(e), sh(b));
    let ints = vec![vec![Value::Int(3)], vec![Value::Int(-1)]];
    let cases = vec![
        // Its own name.
        (
            lam(
                &["c"],
                let_(
                    "x",
                    lit(0i64),
                    Term::If(
                        sh(var("c")),
                        sh(let_("x", add(var("x"), lit(1i64)), var("x"))),
                        sh(var("x")),
                    ),
                ),
            ),
            bools(),
        ),
        // A later binder's name.
        (
            lam(
                &["c"],
                let_(
                    "x",
                    lit(0i64),
                    Term::If(
                        sh(var("c")),
                        sh(let_(
                            "y",
                            add(var("x"), lit(1i64)),
                            let_("x", lit(5i64), add(var("y"), var("x"))),
                        )),
                        sh(var("x")),
                    ),
                ),
            ),
            bools(),
        ),
        // A parameter bound again, read and not read.
        (
            lam(&["x"], let_("x", add(var("x"), lit(1i64)), var("x"))),
            ints.clone(),
        ),
        (
            lam(&["x"], let_("x", lit(1i64), add(var("x"), lit(2i64)))),
            ints.clone(),
        ),
        // A chain of three, each reading the one above.
        (
            lam(
                &["x"],
                let_(
                    "x",
                    add(var("x"), lit(1i64)),
                    let_(
                        "x",
                        add(var("x"), lit(10i64)),
                        let_("x", add(var("x"), lit(100i64)), var("x")),
                    ),
                ),
            ),
            ints.clone(),
        ),
        // Its own name, read only under a binder inside the bound term: not a call.
        (
            lam(
                &["c"],
                let_(
                    "x",
                    let_("x", lit(1i64), add(var("x"), lit(1i64))),
                    add(var("x"), lit(2i64)),
                ),
            ),
            bools(),
        ),
    ];
    for (t, inputs) in &cases {
        for text in [shown(t), pretty_in(t, 20, &none), written(t, |x| x, &none)] {
            reads_back_the_same(t, &text, inputs);
        }
    }
    // The forms, on one line.
    let texts: Vec<String> = cases.iter().map(|(t, _)| shown(t)).collect();
    assert_eq!(
        texts,
        [
            "c -> { x = 0; if c { (x -> x)((x + 1)) } else { x } }",
            "c -> { x = 0; if c { { y = (x + 1); { x = 5; (y + x) } } } else { x } }",
            "x -> (x -> x)((x + 1))",
            "x -> { { x = 1; (x + 2) } }",
            "x -> (x -> (x -> (x -> x)((x + 100)))((x + 10)))((x + 1))",
            "c -> { x = { x = 1; (x + 1) }; (x + 2) }",
        ]
    );

    // A message writes `x@1` and `x@2` both `x` (`zed_kernel::text::ident::written_name`), so
    // they are one name in its text: `x@2 = x@1 + 1` reads its own name there, and
    // `y = x@1 + 1; x@2 = 5` ends the block at `x@2`.
    fn at(x: &str) -> &str {
        x.split_once('@').map_or(x, |(w, _)| w)
    }
    let cases = [
        lam(
            &["x@1"],
            let_("x@2", add(var("x@1"), lit(1i64)), var("x@2")),
        ),
        lam(
            &["x@1"],
            let_(
                "y",
                add(var("x@1"), lit(1i64)),
                let_("x@2", lit(5i64), add(var("y"), var("x@2"))),
            ),
        ),
    ];
    let texts: Vec<String> = cases.iter().map(|t| written(t, at, &none)).collect();
    for (t, text) in cases.iter().zip(&texts) {
        reads_back_the_same(t, text, &ints);
    }
    assert_eq!(
        texts,
        [
            "x -> (x -> x)(x + 1)",
            "x -> { y = x + 1; { x = 5; y + x } }"
        ]
    );
}

/// `L = { a = x + 1; { x = 5; a + x } }`, a `let` held in two places: in the block of `y = 1`
/// in the `then` arm, and first of a block in the `else` arm. The printer meets the `then` arm
/// first, so the walk of `y = 1` reads `L` inside that block; `L` first of a block needs its own
/// walk, or its block does not end at `x = 5`, which `a = x + 1` reads from outside
/// (`{ a = (x + 1); x = 5; (a + x) }` is refused: "used above its definition").
#[test]
fn a_shared_let_first_of_a_block_at_one_place_and_in_a_block_at_another_reads_back() {
    let sh = |t: Term| Shared::new(t);
    let add = |a: Term, b: Term| prim(Prim::Add, vec![a, b]);
    let inner = Term::Let("x".into(), sh(lit(5i64)), sh(add(var("a"), var("x"))));
    let l = sh(Term::Let(
        "a".into(),
        sh(add(var("x"), lit(1i64))),
        sh(inner),
    ));
    let then = sh(Term::Let("y".into(), sh(lit(1i64)), l.clone()));
    let t = Term::Lam(
        vec!["x".into(), "c".into()],
        sh(Term::If(sh(var("c")), then, l)),
    );
    let inputs: Vec<Vec<Value>> = [(3i64, true), (3, false), (-1, true)]
        .map(|(x, c)| vec![Value::Int(x), Value::Bool(c)])
        .to_vec();
    let texts = [
        shown(&t),
        pretty_in(&t, 20, &none),
        written(&t, |x| x, &none),
    ];
    for text in &texts {
        reads_back_the_same(&t, text, &inputs);
    }
    assert_eq!(
        texts[0],
        "(x, c) -> if c { { y = 1; a = (x + 1); { x = 5; (a + x) } } } \
         else { { a = (x + 1); { x = 5; (a + x) } } }"
    );
}

/// The other binders of the kernel against the rule of a block's scope: a `match` arm's
/// pattern and `fam`'s key, written as a lambda. Each binds `x` over a chain of `let`s that
/// binds `x` again, reading it or not, or reads it before a later `let` binds it. Only a
/// function's or a lambda's body block shares the scope of what binds it (zedc-resolve,
/// resolve.rs, the `Task::Function` case); an arm's or an `else`'s value that is a block has a
/// scope of its own (the `ExprKind::Block` case), where it shadows the pattern's names, so the arm is
/// written as any other `let` chain and `fam`'s lambda takes the extra block of
/// [`lambda`](zed_kernel::print).
#[test]
fn a_binding_reading_or_rebinding_a_name_a_pattern_or_fam_binds_reads_back() {
    let sh = |t: Term| Shared::new(t);
    let add = |a: Term, b: Term| prim(Prim::Add, vec![a, b]);
    let let_ = |x: &str, e: Term, b: Term| Term::Let(x.into(), sh(e), sh(b));
    let bodies = || {
        [
            let_("x", add(var("x"), lit(1i64)), var("x")),
            let_("x", lit(1i64), add(var("x"), lit(2i64))),
            let_(
                "y",
                add(var("x"), lit(1i64)),
                let_("x", lit(5i64), add(var("y"), var("x"))),
            ),
        ]
    };
    let x = || Pattern::Bind("x".into());

    // `n -> match n { 0 -> 7, x -> body }`. zedc refuses every `match` ("not supported by
    // this version of zedc"), so these texts are checked as written, not read back.
    let matches: Vec<String> = bodies()
        .into_iter()
        .map(|body| {
            let arms = vec![(Pattern::Lit(Value::Int(0)), lit(7i64)), (x(), body)];
            shown(&Term::Lam(
                vec!["n".into()],
                sh(Term::Match(sh(var("n")), arms)),
            ))
        })
        .collect();
    assert_eq!(
        matches,
        [
            "n -> match n { 0 -> 7, x -> (x -> x)((x + 1)) }",
            "n -> match n { 0 -> 7, x -> { x = 1; (x + 2) } }",
            "n -> match n { 0 -> 7, x -> { y = (x + 1); { x = 5; (y + x) } } }",
        ]
    );

    // An `else` pattern binds no name in this zedc: `#err(n) else #err(x) -> …` is refused ("a
    // struct, name, `_` or tuple pattern is … not supported"), so no term elaborated from one
    // has a binder there.

    // `(n, d) -> fam(d, x -> body)`. zedc refuses the prelude word `fam` ("not supported by
    // this version of zedc"), so these are checked as written too; the lambda is the one
    // [`a_binding_reading_a_name_its_block_binds_reads_back_with_the_same_value`] reads back.
    let fams: Vec<String> = bodies()
        .into_iter()
        .map(|body| {
            let fam = Term::Fam {
                domain: sh(var("d")),
                var: "x".into(),
                body: sh(body),
            };
            shown(&Term::Lam(vec!["n".into(), "d".into()], sh(fam)))
        })
        .collect();
    assert_eq!(
        fams,
        [
            "(n, d) -> fam(d, x -> (x -> x)((x + 1)))",
            "(n, d) -> fam(d, x -> { { x = 1; (x + 2) } })",
            "(n, d) -> fam(d, x -> { y = (x + 1); { x = 5; (y + x) } })",
        ]
    );
}

// Round 2 of XR-lazy-and-kernel-batch-1 on PRINT-let-reading-its-own-name.

fn ints() -> Vec<Vec<Value>> {
    [3i64, -1].map(|n| vec![Value::Int(n)]).to_vec()
}

fn lam_x(body: Term) -> Term {
    Term::Lam(vec!["x".into()], Shared::new(body))
}

/// Claude D-2, Codex D6: at width 20 a call `(x -> rest)(e)` that binds the parameter again
/// is broken into lines inside its lambda, and reads back.
#[test]
fn a_call_binding_the_parameter_again_broken_at_width_20_reads_back() {
    let cases = [
        lam_x(let_(
            "x",
            add(var("x"), lit(1i64)),
            let_("x", add(var("x"), lit(10i64)), var("x")),
        )),
        lam_x(let_(
            "x",
            add(var("x"), lit(1i64)),
            let_("long_name", lit(123456i64), add(var("long_name"), var("x"))),
        )),
    ];
    let texts: Vec<String> = cases.iter().map(|t| pretty_in(t, 20, &none)).collect();
    for (t, text) in cases.iter().zip(&texts) {
        reads_back_the_same(t, text, &ints());
    }
    // Written by hand from the layout rules, not from a run. Each binding reading `x` is a
    // call (`Pieces::called`), so no block binds the parameter. In the first, the call
    // `((x + 10))` would start at column 19 and does not fit, so its one item goes on its own
    // line indented two. Read by eye: `x -> (x -> (x -> x)((x + 10)))((x + 1))`, which is
    // `x + 11`, as `let x = x + 1 in let x = x + 10 in x`. In the second, the block of
    // `long_name` does not fit after `x -> (x -> `, so each of its statements goes on its own
    // line; `long_name = 123456;` is one `Cat` of texts with no break in it, so that line is
    // 21 columns, past the width, as `render` allows ("where it can"). Read by eye:
    // `x -> (x -> { long_name = 123456; (long_name + x) })((x + 1))`, which is
    // `x + 123457`, as the term; the block binds `long_name` only, not the parameter.
    assert_eq!(
        texts,
        [
            "x -> (x -> (x -> x)(\n  (x + 10)\n))((x + 1))",
            "x -> (x -> {\n  long_name = 123456;\n  (long_name + x)\n})((x + 1))",
        ]
    );
}

/// Codex D1: a binding whose bound term binds `x` inside itself and reads it there reads the
/// `x` outside only with one more read of `x`, before the inner binder or after it: then the
/// block ends at `x = 5`, and with none it does not.
#[test]
fn a_binding_reading_x_only_under_its_own_binder_of_x_keeps_the_block() {
    let inner = || let_("x", lit(1i64), var("x"));
    let of = |e: Term| {
        let arm = let_("y", e, let_("x", lit(5i64), add(var("y"), var("x"))));
        Term::Lam(
            vec!["c".into()],
            Shared::new(let_(
                "x",
                lit(0i64),
                Term::If(
                    Shared::new(var("c")),
                    Shared::new(arm),
                    Shared::new(var("x")),
                ),
            )),
        )
    };
    let cases = [
        of(add(var("x"), inner())),
        of(add(inner(), var("x"))),
        of(add(inner(), lit(1i64))),
    ];
    let texts: Vec<String> = cases.iter().map(|t| written(t, |x| x, &none)).collect();
    for (t, text) in cases.iter().zip(&texts) {
        reads_back_the_same(t, text, &bools());
        reads_back_the_same(t, &shown(t), &bools());
    }
    // Written by hand from the rules, not from a run. An `if` branch is written in its braces
    // (`Pieces::block`) and a `let` in its own, so a branch that is a `let` is `{ { … } }`. In
    // the first two `y = …` reads the `x` outside, so `x = 5` would be used above its
    // definition in the same block: the block ends before it and `{ x = 5; y + x }` is nested.
    // In the third `y = …` reads only the `x` of its own block `{ x = 1; x }`, so `x = 5` joins
    // the block of `y`. Read by eye, each in block scope: with `c` true the first two give
    // `y = 0 + 1 = 1`, then `1 + 5 = 6`, and the third `y = 1 + 1 = 2`, then `2 + 5 = 7`, as the
    // terms; with `c` false each gives the outer `x`, 0.
    assert_eq!(
        texts,
        [
            "c -> { x = 0; if c { { y = x + { x = 1; x }; { x = 5; y + x } } } else { x } }",
            "c -> { x = 0; if c { { y = { x = 1; x } + x; { x = 5; y + x } } } else { x } }",
            "c -> { x = 0; if c { { y = { x = 1; x } + 1; x = 5; y + x } } else { x } }",
        ]
    );
}

/// Gemini D.3, Codex D4: in `Display`, which labels a part reading a name bound in two places,
/// a labeled `let` that is the body of another `let` at its first place is written with its
/// label there, `#1=`, and `#1#` at its other place.
#[test]
fn a_labeled_let_held_as_the_body_of_a_let_is_written_with_its_label() {
    // `L` has 13 nodes: a part held in 2 places that reads a rebound name is written once
    // when `s + 4 + 2 * 3 < 2 * s` (`dag::choose`), so it needs `s >= 11`; with fewer it is
    // written in full at each place and has no label.
    let l = Shared::new(let_(
        "z",
        add(var("w"), lit(1i64)),
        let_(
            "u",
            add(var("z"), lit(2i64)),
            add(add(var("z"), var("u")), lit(3i64)),
        ),
    ));
    let t = Term::Lam(
        vec!["c".into(), "w".into()],
        Shared::new(Term::If(
            Shared::new(var("c")),
            Shared::new(let_(
                "w",
                lit(1i64),
                Term::Let("a".into(), Shared::new(lit(0i64)), l.clone()),
            )),
            l,
        )),
    );
    // Written by hand from the rules, not from a run. The block of `w` and `a` ends at `L`,
    // which is labeled, and `L` is written there as a term, `#1=` and its own block; the
    // `else` branch writes `#1#`. Read by eye, `#1#` replaced by the text after `#1=`: with
    // `c` true `w = 1`, `z = 2`, `u = 4`, giving 9; with `c` false `z = w + 1`, `u = w + 3`,
    // giving `2 w + 7`, as the term, the `w` of `L` being the nearer binder at each place.
    assert_eq!(
        format!("{t}"),
        "(c, w) -> if c { { w = 1; a = 0; #1={ z = (w + 1); u = (z + 2); ((z + u) + 3) } } } \
         else { #1# }"
    );
    // A user's text, with no label, reads back to the same value.
    let inputs: Vec<Vec<Value>> = [(true, 3i64), (false, -1)]
        .map(|(c, w)| vec![Value::Bool(c), Value::Int(w)])
        .to_vec();
    reads_back_the_same(&t, &shown(&t), &inputs);
}

/// Gemini D.1, Claude D-3: a parameter bound again after the first block of the body has
/// ended (at a name bound twice, or at a binder a binding above reads from outside) is bound
/// in a nested block already, so the body takes no more braces; bound again in the first
/// block, it does.
#[test]
fn a_parameter_bound_again_after_the_first_block_ends_takes_no_more_braces() {
    let cases = [
        lam_x(let_(
            "y",
            lit(1i64),
            let_(
                "y",
                lit(2i64),
                let_("x", lit(3i64), add(var("x"), var("y"))),
            ),
        )),
        lam_x(let_(
            "y",
            add(var("x"), lit(1i64)),
            let_("x", lit(5i64), add(var("y"), var("x"))),
        )),
        lam_x(let_(
            "y",
            lit(1i64),
            let_("x", add(var("y"), lit(2i64)), var("x")),
        )),
    ];
    let texts: Vec<String> = cases.iter().map(|t| written(t, |x| x, &none)).collect();
    for (t, text) in cases.iter().zip(&texts) {
        reads_back_the_same(t, text, &ints());
        reads_back_the_same(t, &shown(t), &ints());
    }
    // Written by hand from the rules, not from a run. The first block ends at the second `y`
    // and in the second case at `x = 5`, which `y = x + 1` reads from outside, so `x = 3` and
    // `x = 5` are in nested blocks and the body takes no more braces; in the third `x = y + 2`
    // is in the first block, which shares its scope with the parameter, so the body is
    // nested once more. Read by eye, in block scope: 3 + 2 = 5, x + 1 + 5, and 1 + 2 = 3, as
    // the terms.
    assert_eq!(
        texts,
        [
            "x -> { y = 1; { y = 2; x = 3; x + y } }",
            "x -> { y = x + 1; { x = 5; y + x } }",
            "x -> { { y = 1; x = y + 2; x } }",
        ]
    );
}

/// The walk of `Pieces::lambda` stops at a labeled body as the block does: a parameter bound
/// again inside the labeled part is in the part's own block, so the body takes no more braces.
#[test]
fn a_parameter_bound_again_inside_a_labeled_body_takes_no_more_braces() {
    // 15 nodes, so the part held in 2 places is written once (`dag::choose` needs 11).
    let l = Shared::new(let_(
        "w",
        lit(1i64),
        let_(
            "z",
            add(var("w"), lit(1i64)),
            let_(
                "u",
                add(var("z"), lit(2i64)),
                add(add(var("z"), var("u")), lit(3i64)),
            ),
        ),
    ));
    let t = Term::Lam(
        vec!["c".into(), "w".into()],
        Shared::new(Term::Let("a".into(), l.clone(), l)),
    );
    // Written by hand from the rules, not from a run: the block of `a` ends at the labeled
    // body, written `#1#`, and the walk of the lambda ends there too, so `w = 1`, inside the
    // part's own block, does not nest the body. Read by eye, `#1#` replaced by the text
    // after `#1=`: `a = 9`, then 9, as the term.
    assert_eq!(
        format!("{t}"),
        "(c, w) -> { a = #1={ w = 1; z = (w + 1); u = (z + 2); ((z + u) + 3) }; #1# }"
    );
    let inputs: Vec<Vec<Value>> = [(true, 3i64), (false, -1)]
        .map(|(c, w)| vec![Value::Bool(c), Value::Int(w)])
        .to_vec();
    reads_back_the_same(&t, &shown(&t), &inputs);
}
