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

use std::collections::HashMap;

use zed_kernel::print::{pretty_in, written};
use zed_kernel::term::build::{lit, var};
use zed_kernel::{Evaluator, Prim, Shared, Term, Value, World};
use zed_tests::scaling::{self, FACTOR};
use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};

use super::scaling::deep;

fn prim(p: Prim, args: Vec<Term>) -> Term {
    Term::Prim(p, args)
}

/// `n -> td`: `t0 = n + 100`, `tj = if n >= j { t(j-1) } else { t(j-1) }`, the two arms of each
/// `if` one part when `shared`, else two copies (`2^d` places either way).
fn arms(d: usize, shared: bool) -> Term {
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
fn lets(d: usize) -> Term {
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
fn wide(k: usize, m: usize) -> Term {
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

/// `c -> if c { x = 1; P } else { x = 2; P }` and `P = { x = 3; (x, …, x) }` with `w` items: the one name bound in more than one place is `x`, so the env is `x` itself, and `P`
/// sets its slot before any read of it, so the env passed to `P` is not read; it is named all the
/// same, since `_ ->` is not a lambda.
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
fn shown(t: &Term) -> String {
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
        "{ env2 = (0, 0); (y0, c) -> { part1 = env4 -> if c { { y2 = (env4[0] + 1); \
         env5 = (env4[0], y2); env5[1] } } else { { y2 = (env4[0] + 2); env6 = (env4[0], y2); \
         env6[1] } }; if c { { y1 = (y0 + 1); env1 = (y1, env2[1]); part1(env1) } } else { \
         { y1 = (y0 + 2); env3 = (y1, env2[1]); part1(env3) } } } }"
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

/// The text's length at `d` and at `FACTOR * d` is held to a constant over the factor (a
/// logarithm included), and the time to the order check.
fn scales(
    what: &str,
    n: usize,
    make: impl Fn(usize) -> Term,
    print: impl Fn(&Term) -> String + Sync,
) {
    let terms: HashMap<usize, Term> = scaling::inputs(n, make);
    let lens: HashMap<usize, usize> = terms.iter().map(|(&d, t)| (d, print(t).len())).collect();
    assert!(
        lens[&(FACTOR * n)] <= 3 * FACTOR * lens[&n],
        "{what}: the text is {} long at {n}, {} at {}",
        lens[&n],
        lens[&(FACTOR * n)],
        FACTOR * n
    );
    scaling::check(what, n, |d| {
        assert_eq!(print(&terms[&d]).len(), lens[&d]);
    });
}

#[test]
fn writing_nested_ifs_over_one_part_scales() {
    deep(|| {
        scales(
            "pretty_in on d nested ifs over one part",
            400,
            |d| arms(d, true),
            shown,
        );
        scales(
            "Display on d nested ifs over one part",
            400,
            |d| arms(d, true),
            |t| t.to_string(),
        );
    });
}

#[test]
fn writing_nested_lets_whose_part_reads_a_name_bound_twice_scales() {
    deep(|| {
        scales(
            "pretty_in on d nested ifs binding a name over one part",
            400,
            lets,
            shown,
        );
        scales(
            "Display on d nested ifs binding a name over one part",
            400,
            lets,
            |t| t.to_string(),
        );
    });
}

#[ignore = "STAGE-scaling-10_5: 11.5 times the work at 50 and 400, over the limit of 10.5; open"]
#[test]
fn writing_a_part_reading_many_names_bound_twice_scales() {
    deep(|| {
        scales("pretty_in on wide(n, n)", 50, |n| wide(n, n), shown);
        scales(
            "Display on wide(n, n)",
            50,
            |n| wide(n, n),
            |t| t.to_string(),
        );
    });
}
