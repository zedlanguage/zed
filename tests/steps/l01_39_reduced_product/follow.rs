//! A generic literal compared by `==` or `!=` with a parameter whose carrier is inferred
//! follows the parameter's carrier (DESIGN.md L1.26a): the elaborator writes `x == 3` as a
//! match on `x` that gives `3.0`, `3r` or `3`. The scope reads that test as the plain `x == 3`
//! where `x` is an integer, and the preimage catalog reads it so where `x` is any integer term.
//! The value compared is found once: a chain of such tests, each comparing the `if` below with
//! a literal, costs what the plain chain costs (repair of LIT-adopt; COMPLEXITY.md row F69). A
//! parameter declared `int` takes the plain test, with no `match`.

use std::sync::Arc;

use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Prim, Shared, Term, Value, World};
use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::store::images::{self, TermRead};
use zedc::store::interval::{End, IntervalSet};
use zedc::store::preimage::{
    Demand, Domains, LetIn, LetPa, Lets, let_narrowing, let_preimage, let_summary,
};
use zedc::store::product::{Product, Scope, arms};

use super::{arm, generic_arms_of as arms_of, ints};
use zed_tests::step_helpers::l01_25_preimage_catalog::function;

/// The test of each arm, the outcome, and the integers each named parameter holds there.
fn readings(src: &str, names: &[&str]) -> Vec<String> {
    let (_, _, a) = arms_of(src);
    a.iter()
        .map(|a| {
            let held: Vec<String> = names
                .iter()
                .map(|n| format!("{n} {}", a.scope.get(n).ints()))
                .collect();
            format!("{}: {}", a.outcome, held.join(", "))
        })
        .collect()
}

#[test]
fn a_retry_counter_compared_with_a_literal_is_narrowed_to_it() {
    // `tries` is inferred: the function takes any number, and `3` follows its carrier.
    let src = "ok(positional tries) = if tries == 3 { 10 } else { 20 };";
    let (_, body, _) = arms_of(src);
    assert!(body.to_string().contains("is f64 -> 3.0"), "{body}");
    assert_eq!(
        readings(src, &["tries"]),
        ["true: tries [3..=3]", "false: tries [..=2, 4..]"]
    );
    // `!=` on either side.
    let src = "ok(positional slot) = if slot != 3 && 4 != slot { 10 } else { 20 };";
    assert_eq!(
        readings(src, &["slot"]),
        ["true: slot [..=2, 5..]", "false: slot [3..=4]"]
    );
}

#[test]
fn a_difference_compared_with_a_literal_is_narrowed_by_its_preimage() {
    // The value compared is a term, not a name: the preimage catalog reads the match as the
    // literal itself, and the linear relation is the plain test's.
    let src = "ok(positional a, positional b) = if a - b == 3 && a == 5 { 10 } else { 20 };";
    assert_eq!(
        readings(src, &["a", "b"]),
        ["true: a [5..=5], b [2..=2]", "false: a [..], b [..]"]
    );
    let src = "ok(positional debt) = if -debt == 3 { 10 } else { 20 };";
    assert_eq!(
        readings(src, &["debt"]),
        ["true: debt [-3..=-3]", "false: debt [..=-4, -2..]"]
    );
}

#[test]
fn at_a_float_the_test_is_not_read_as_an_integer_equality() {
    // At an `f64` the literal is `3.0`: the true arm is reached, at `3.0`, though no integer
    // is in it.
    let (ps, body) = function("ok(positional level) = if level == 3 { 10 } else { 20 };");
    let floats = Scope::new(
        ps.iter()
            .map(|p| (p.clone(), Product::of_type(Type::f64()))),
    );
    let a = arms(&body, &floats);
    let then = arm(&a, "3.0", true);
    assert!(then.reachable(), "{}", then.scope);
    assert!(arm(&a, "3.0", false).reachable());
}

/// `ok(positional n) = if (if (… n …) == 1 { n } else { n + n }) == 1 { n } else { n + n }`,
/// `d` deep; with `n: int` declared when `plain`, else `n` inferred, so each `1` follows.
fn chain(d: usize, plain: bool) -> String {
    let inner = (0..d).fold("n".to_string(), |x, _| {
        format!("if ({x}) == 1 {{ n }} else {{ n + n }}")
    });
    let ty = if plain { ": int" } else { "" };
    format!("ok(positional n{ty}) = {inner};")
}

/// The terms of `ok` for sizes `n` and `8 n`, built before timing.
fn sizes(n: usize, src: fn(usize) -> String) -> (Scope, [(usize, Arc<Term>); 2]) {
    let (ps, small) = function(&src(n));
    let (_, large) = function(&src(scaling::FACTOR * n));
    (
        ints(&ps),
        [(n, Arc::new(small)), (scaling::FACTOR * n, Arc::new(large))],
    )
}

fn at(terms: &[(usize, Arc<Term>); 2], k: usize) -> &Term {
    &terms.iter().find(|(n, _)| *n == k).expect("a built size").1
}

/// `if slot != 0 && slot != 1 && … { 10 } else { 20 }`, `k` tests.
fn excluded(k: usize) -> String {
    let tests: Vec<String> = (0..k).map(|i| format!("slot != {i}")).collect();
    format!(
        "ok(positional slot) = if {} {{ 10 }} else {{ 20 }};",
        tests.join(" && ")
    )
}

/// `{ b0 = a - b == 0; …; if b(k-1) { 10 } else { 20 } }`: each binding a following test of
/// a difference, which the scope finds the value of.
fn bound(k: usize) -> String {
    let lets: String = (0..k).map(|i| format!("b{i} = a - b == {i}; ")).collect();
    format!(
        "ok(positional a, positional b) = {{ {lets}if b{} {{ 10 }} else {{ 20 }} }};",
        k - 1
    )
}

/// `if a - b != 0 && a - b != 1 && … { 10 } else { 20 }`: following tests of a difference,
/// each read by the preimage catalog.
fn differences(k: usize) -> String {
    let tests: Vec<String> = (0..k).map(|i| format!("a - b != {i}")).collect();
    format!(
        "ok(positional a, positional b) = if {} {{ 10 }} else {{ 20 }};",
        tests.join(" && ")
    )
}

/// `ok(positional n: int, …) = if (if (… n …) == 1 { n } else { e }) == 1 { n } else { e }`,
/// `d` deep, with the parameters `ps`.
fn nested(d: usize, e: &str, ps: &str) -> String {
    let inner = (0..d).fold("n".to_string(), |x, _| {
        format!("if ({x}) == 1 {{ n }} else {{ {e} }}")
    });
    format!("ok({ps}) = {inner};")
}

/// Each sum of the chains read below: its parameters and the names whose integers are read.
const SUMS: [(&str, &str, &[&str]); 6] = [
    ("n + n", "positional n: int", &["n"]),
    ("n - n", "positional n: int", &["n"]),
    ("n + n + n", "positional n: int", &["n"]),
    ("2 * n - n", "positional n: int", &["n"]),
    ("n - 3 * n + 4", "positional n: int", &["n"]),
    ("n + m", "positional n: int, positional m: int", &["n", "m"]),
];

/// A sum of one input with itself is a line of it, so each test of the chain reads its
/// preimage exactly: the outer test holds at `n = 1` alone, at every depth. The readings are
/// those of the reading before sums of lines were summarized, at depths 1 to 12 (repair of
/// PRODUCT-nested-chain; COMPLEXITY.md row F70). A sum of two inputs is no summary, and keeps
/// its readings: at depth 2 its true arm reads every `n`. At an odd depth from 3 the outer test
/// holds at `n = 1` alone: with `n != 1` the test inside it is `n + m == 1`, and the value
/// tested is `n` where that holds and `n + m` where it does not, `1` in neither; at an even
/// depth the value tested is `n + m` again, `1` for some `m`. Since PRES-pendants-wider, which
/// tightens a hull end found by cases, depth 3 reads `n` exactly. The odd depths from 5 still
/// read every `n`: sound, but wider than `n = 1`, since the ends there are bounded only by a
/// combination of cases that the end search does not try (a follow-up of PRES-pendants-wider).
#[test]
fn nested_sums_keep_their_arms() {
    for (e, ps, names) in SUMS {
        for d in 1..=12 {
            let want = match (e, d) {
                ("n + m", 1 | 3) => ["true: n [1..=1], m [..]", "false: n [..=0, 2..], m [..]"],
                ("n + m", _) => ["true: n [..], m [..]", "false: n [..=0, 2..], m [..]"],
                _ => ["true: n [1..=1]", "false: n [..=0, 2..]"],
            };
            assert_eq!(readings(&nested(d, e, ps), names), want, "{e} at depth {d}");
        }
    }
}

/// The value of the test of the outermost `if` of `ok`'s body at `n = x`, by the interpreter.
fn outer_test_at(body: &Term) -> impl Fn(i64) -> bool {
    fn test_of(t: &Term) -> Term {
        match t {
            Term::Let(n, e, b) => Term::Let(n.clone(), e.clone(), Shared::new(test_of(b))),
            Term::If(c, _, _) => (**c).clone(),
            _ => panic!("no `if` in {t}"),
        }
    }
    let test = test_of(body);
    move |x| {
        let t = Term::Let(
            "n".into(),
            Shared::new(Term::Lit(Value::Int(x))),
            Shared::new(test.clone()),
        );
        match Evaluator::new(World::new()).run(&t) {
            Ok(Value::Bool(b)) => b,
            v => panic!("the test at n = {x} gave {v:?}"),
        }
    }
}

/// Checks the two arms of the outermost `if` of `src` against the interpreter on
/// `-WINDOW..=WINDOW`: the true arm holds exactly the `n` where the test holds, and the false
/// arm exactly the others, so neither reads more integers than it reaches.
fn exact_on_window(src: &str) -> Result<(), String> {
    const WINDOW: i64 = 30;
    let (_, body, a) = arms_of(src);
    let holds = outer_test_at(&body);
    let (yes, no) = (&a[0], &a[1]);
    assert!(
        yes.outcome && !no.outcome,
        "{src}: the first two arms are the outer ones"
    );
    let (yes, no) = (yes.scope.get("n"), no.scope.get("n"));
    let (yes, no) = (yes.ints(), no.ints());
    for x in -WINDOW..=WINDOW {
        let h = holds(x);
        if yes.contains(x) != h || no.contains(x) != !h {
            return Err(format!(
                "{src}: at n = {x} the test gives {h}, the arms read [{yes}] and [{no}]"
            ));
        }
    }
    Ok(())
}

/// A sum with an `if` among its operands is summarized: the line `n` is added to each piece
/// of the `if` by one tag ([`Pa::plus`]), so the outer test reads its preimage exactly, `n = 1`
/// alone, at every depth, where before from depth 4 its true arm read every `n` (the sum had
/// no summary, the projection read `n` as every integer, and the linear stage refused the
/// three tied disjunctions; repair of PA-plus-if).
#[test]
fn nested_sums_with_an_if_keep_their_arms() {
    let e = "n + (if n > 0 { n } else { 0 })";
    for d in 1..=64 {
        let src = nested(d, e, "positional n: int");
        let want = [
            "true: n [1..=1]",
            "false: n [..=0, 2..]",
            "true: n [2..]",
            "false: n [..=0]",
        ];
        assert_eq!(readings(&src, &["n"]), want, "{e} at depth {d}");
        exact_on_window(&src).unwrap();
    }
    // A sum of two piecewise summaries is one, cut at the ends of both.
    for d in 1..=32 {
        exact_on_window(&ramps(d)).unwrap();
    }
}

/// A random term `if n > c { a * n + b } else { a' * n + b' }`, or with `<`.
fn random_if(rng: &mut Rng) -> String {
    let mut line = || {
        let (a, b) = (rng.int(-3, 3), rng.int(-9, 9));
        format!("{a} * n + {b}")
    };
    let (yes, no) = (line(), line());
    let op = if rng.below(2) == 0 { ">" } else { "<" };
    format!(
        "(if n {op} {} {{ {yes} }} else {{ {no} }})",
        rng.int(-12, 12)
    )
}

/// Sums and differences of two to five random `if` terms and lines of `n`, compared with a
/// random integer, read exactly on a window by the interpreter: each sum of two summaries is
/// one ([`Pa::plus`]), so the preimage of the comparison is that of the summary.
#[test]
fn random_sums_of_piecewise_terms_are_read_exactly() {
    let mut rng = Rng::new(0x5eed_0f5a_5a5a);
    for round in 0..400 {
        let mut sum = random_if(&mut rng);
        for _ in 0..1 + rng.below(4) {
            let op = if rng.below(2) == 0 { "+" } else { "-" };
            let term = if rng.below(4) == 0 {
                format!("({} * n)", rng.int(-3, 3))
            } else {
                random_if(&mut rng)
            };
            sum = format!("{sum} {op} {term}");
        }
        let cmp = rng.pick(&["==", "!=", "<", ">="]);
        let src = format!(
            "ok(positional n: int) = if {sum} {cmp} {} {{ 1 }} else {{ 2 }};",
            rng.int(-20, 20)
        );
        if let Err(e) = exact_on_window(&src) {
            panic!("round {round}: {e}");
        }
    }
}

fn twice(d: usize) -> String {
    nested(d, "n + n", "positional n: int")
}

fn line(d: usize) -> String {
    nested(d, "n - 3 * n + 4", "positional n: int")
}

fn two(d: usize) -> String {
    nested(d, "n + m", "positional n: int, positional m: int")
}

fn following(d: usize) -> String {
    chain(d, false)
}

fn with_an_if(d: usize) -> String {
    nested(d, "n + (if n > 0 { n } else { 0 })", "positional n: int")
}

/// `if (if n > 0 { n } else { 0 }) + (if n > 1 { n } else { 0 }) + … == 1 { 1 } else { 2 }`,
/// `d` ramps: each sum adds a summary of two pieces to one of up to `d` pieces.
fn ramps(d: usize) -> String {
    let sum: Vec<String> = (0..d)
        .map(|i| format!("(if n > {i} {{ n }} else {{ 0 }})"))
        .collect();
    format!(
        "ok(positional n: int) = if {} == 1 {{ 1 }} else {{ 2 }};",
        sum.join(" + ")
    )
}

/// `ok` with the block `y0 = 0; x0 = 0; y_k = y_(k-1) + ramp_k; x_k = x_(k-1) + y_k` for
/// `k = 1..=d`, `ramp_k = if n > k - 1 { n } else { 0 }`, then `if x_d == 1 { 1 } else { 2 }`.
/// `x_d` is 0 for `n <= 0` and `d (d + 1) / 2 * n` at `n >= d`, so at `d >= 2` no `n` meets
/// the test, and at `d = 1` only `n = 1`.
fn let_chain(d: usize) -> String {
    let mut s = String::from("y0 = 0; x0 = 0; ");
    for k in 1..=d {
        let j = k - 1;
        s += &format!("y{k} = y{j} + (if n > {j} {{ n }} else {{ 0 }}); x{k} = x{j} + y{k}; ");
    }
    format!("ok(positional n: int) = {{ {s}if x{d} == 1 {{ 1 }} else {{ 2 }} }};")
}

/// As [`exact_on_window`], for the `if` that ends a block of `let`s: its arms are the last
/// two, after those of the tests in the bound terms, and its own arms hold no test. Without
/// `exact`, only that each arm holds every `n` that reaches it.
fn block_on_window(src: &str, exact: bool) -> Result<(), String> {
    const WINDOW: i64 = 30;
    let (_, body, a) = arms_of(src);
    let holds = outer_test_at(&body);
    let [.., yes, no] = &a[..] else {
        return Err(format!("{src}: fewer than two arms"));
    };
    assert!(
        yes.outcome && !no.outcome,
        "{src}: the last two arms are the final test's"
    );
    let (yes, no) = (yes.scope.get("n"), no.scope.get("n"));
    let (yes, no) = (yes.ints(), no.ints());
    for x in -WINDOW..=WINDOW {
        let h = holds(x);
        let (y, n) = (yes.contains(x), no.contains(x));
        if (h && !y) || (!h && !n) || (exact && (y != h || n == h)) {
            return Err(format!(
                "{src}: at n = {x} the test gives {h}, the arms read [{yes}] and [{no}]"
            ));
        }
    }
    Ok(())
}

fn block_exact_on_window(src: &str) -> Result<(), String> {
    block_on_window(src, true)
}

/// A name bound by a `let` carries the summary of its value, over the input it is computed
/// from, into the tests that read it: `x == 1` after `y = n + 1; x = y + n` narrows `n` to
/// 0, where before the name was read as an input of its own and `n` kept every integer
/// (repair of PA-let-block).
#[test]
fn a_name_bound_by_let_carries_its_summary() {
    let src = "ok(positional n: int) = { y = n + 1; x = y + n; if x == 1 { 1 } else { 2 } };";
    assert_eq!(
        readings(src, &["n"]),
        ["true: n [0..=0]", "false: n [..=-1, 1..]"]
    );
    for src in [
        src,
        // A price with a fee above ten items.
        "ok(positional n: int) = { base = 3 * n + 2; fee = if n > 10 { 5 } else { 0 }; \
         total = base + fee; if total == 20 { 1 } else { 2 } };",
        // An offset of a clamped index.
        "ok(positional n: int) = { lo = if n < 0 { 0 } else { n }; hi = lo - 4; \
         if hi >= 3 { 1 } else { 2 } };",
        // A name bound again in a nested block, and the binding it shadows after it.
        "ok(positional n: int) = { y = n + 1; z = { y = 2 * n; y + 3 }; w = z + y; \
         if w == 10 { 1 } else { 2 } };",
        // A difference of two names of one input.
        "ok(positional n: int) = { a = 2 * n - 1; b = n + 4; d = a - b; \
         if d < 0 { 1 } else { 2 } };",
        // A literal binding and a name bound to a name.
        "ok(positional n: int) = { k = 7; m = n; s = m + k; t = -s; \
         if t != -9 { 1 } else { 2 } };",
        // Tests inside the bound terms and of names bound inside an `if`.
        "ok(positional n: int) = { s = if n > 2 { u = n - 2; u * 3 } else { 0 }; \
         t = s + n; if t == 14 { 1 } else { 2 } };",
    ] {
        block_exact_on_window(src).unwrap();
    }
    // A bound term the summary does not cover: its name is an input of its own, and each
    // arm keeps every `n` that reaches it.
    for src in [
        "ok(positional n: int) = { q = n * n; r = q + n; if r == 6 { 1 } else { 2 } };",
        "ok(positional n: int) = { q = n div 3; r = q + n; if r == 9 { 1 } else { 2 } };",
        "ok(positional n: int) = { q = n * n; r = q + n; s = r + 1; if s == 7 { 1 } else { 2 } };",
    ] {
        block_on_window(src, false).unwrap();
    }
}

/// The chain of sums of ramps ([`let_chain`]) reads its answer exactly: only `n = 1` at
/// `d = 1`, and no `n` from `d = 2`, where before the final test's true arm kept every `n`.
#[test]
fn a_block_of_sums_of_ramps_reads_no_n() {
    let last = |d: usize| readings(&let_chain(d), &["n"]).split_off(2 * d);
    assert_eq!(last(1), ["true: n [1..=1]", "false: n [..=0, 2..]"]);
    for d in 2..=48 {
        assert_eq!(last(d), ["true: n []", "false: n [..]"], "at d = {d}");
        block_exact_on_window(&let_chain(d)).unwrap();
    }
}

/// A random block of one to five `let`s, each a sum of one to three of an earlier name, a
/// multiple of one, a multiple of `n`, an `if` of two lines of `n` and a literal, then a test
/// of the last name against a literal.
fn random_block(rng: &mut Rng) -> String {
    let mut s = String::new();
    let k = 1 + rng.below(5);
    for i in 0..k {
        let mut terms = Vec::new();
        for _ in 0..1 + rng.below(3) {
            let pick = rng.below(5);
            terms.push(match pick {
                0 if i > 0 => format!("v{}", rng.below(i)),
                1 if i > 0 => format!("{} * v{}", rng.int(-2, 2), rng.below(i)),
                2 => format!("{} * n", rng.int(-3, 3)),
                3 => random_if(rng),
                _ => format!("{}", rng.int(-9, 9)),
            });
        }
        let op = if rng.below(2) == 0 { " + " } else { " - " };
        s += &format!("v{i} = {}; ", terms.join(op));
    }
    let cmp = rng.pick(&["==", "!=", "<", ">="]);
    format!(
        "ok(positional n: int) = {{ {s}if v{} {cmp} {} {{ 1 }} else {{ 2 }} }};",
        k - 1,
        rng.int(-20, 20)
    )
}

/// Random blocks of `let`s ([`random_block`]) read exactly on a window by the interpreter.
#[test]
fn random_blocks_of_lets_are_read_exactly() {
    let mut rng = Rng::new(0x1e7_b10c);
    for round in 0..400 {
        let src = random_block(&mut rng);
        if let Err(e) = block_exact_on_window(&src) {
            panic!("round {round}: {e}");
        }
    }
}

/// The summary of `x_d` in the chain `x_0 = n; x_k = x_(k-1) + 1`, built one binding at a
/// time ([`let_summary`]), and the inputs where `x_d == d + 5` read through it
/// ([`let_preimage`]).
fn deep_chain(d: usize) -> Domains {
    let n: Arc<str> = "n".into();
    let inputs: Domains = [(n.clone(), IntervalSet::top())].into();
    let var = |x: &Arc<str>| Term::Var(x.clone());
    let mut x: Arc<str> = "x0".into();
    let mut summary = let_summary(&Term::Var(n), &inputs, Lets::new()).expect("a summary of n");
    for k in 1..=d {
        let next: Arc<str> = format!("x{k}").into();
        let e = Term::Prim(Prim::Add, vec![var(&x), Term::Lit(Value::Int(1))]);
        let lets = Lets::from([(
            x.clone(),
            LetIn {
                summary,
                ints: IntervalSet::top(),
                read: None,
            },
        )]);
        summary = let_summary(&e, &inputs, lets).expect("a summary of a sum");
        x = next;
    }
    let target = Term::Lit(Value::Int(d as i64 + 5));
    let test = Term::Prim(Prim::Eq, vec![var(&x), target]);
    let lets = Lets::from([(
        x,
        LetIn {
            summary,
            ints: IntervalSet::top(),
            read: None,
        },
    )]);
    let_preimage(&test, &inputs, lets, &Demand::Bool(true))
}

/// A chain of summaries as deep as a block of 200 000 bindings is formed and dropped on
/// explicit stacks, with no overflow, and reads `n = 5`.
#[test]
fn a_deep_chain_of_summaries_is_formed_and_dropped() {
    let got = deep_chain(200_000);
    assert_eq!(got["n"].to_string(), "[5..=5]");
}

/// A random domain: one to three pieces with ends in `-40..=40`, an end now and then
/// unbounded, beyond `i64`, or at an end of `i128`, which a line's inversion does not take.
fn random_domain(rng: &mut Rng) -> IntervalSet {
    let end = |rng: &mut Rng, lo: bool| match rng.below(14) {
        0 if lo => End::NegInf,
        0 => End::PosInf,
        1 => End::from(if lo { -(1i128 << 70) } else { 1i128 << 70 }),
        2 => End::from(if lo { i128::MIN } else { i128::MAX }),
        _ => End::from(rng.int(-40, 40)),
    };
    let pieces = (0..1 + rng.below(3))
        .map(|_| {
            let (a, b) = (end(rng, true), end(rng, false));
            if a <= b { (a, b) } else { (b, a) }
        })
        .collect();
    let d = IntervalSet::from_pieces(pieces);
    if d.is_empty() {
        IntervalSet::single(0)
    } else {
        d
    }
}

/// `a * x + b`, or `if x > c { a * x + b } else { a' * x + b' }` (or with `<`), for random
/// small integers.
fn random_term(rng: &mut Rng, x: &Arc<str>) -> Term {
    let lit = |v: i64| Term::Lit(Value::Int(v));
    let line = |rng: &mut Rng| {
        let a = Term::Prim(Prim::Mul, vec![lit(rng.int(-3, 3)), Term::Var(x.clone())]);
        Term::Prim(Prim::Add, vec![a, lit(rng.int(-9, 9))])
    };
    if rng.below(2) == 0 {
        return line(rng);
    }
    let op = if rng.below(2) == 0 {
        Prim::Gt
    } else {
        Prim::Lt
    };
    let test = Term::Prim(op, vec![Term::Var(x.clone()), lit(rng.int(-20, 20))]);
    let (yes, no) = (line(rng), line(rng));
    Term::If(Shared::new(test), Shared::new(yes), Shared::new(no))
}

/// The sum of a random term of each of `xs`, and its summary over `doms`.
fn random_sum(rng: &mut Rng, xs: &[Arc<str>], doms: &Domains) -> Option<LetPa> {
    let sum = (xs.iter().map(|x| random_term(rng, x)))
        .reduce(|s, t| Term::Prim(Prim::Add, vec![s, t]))?;
    let_summary(&sum, doms, Lets::new())
}

/// Tests through summaries over many inputs, read through the trees of their terms' bounds
/// ([`let_narrowing`], [`TermRead`]), narrow the inputs exactly as reading every input does
/// ([`let_preimage`] with each input among the inputs): random sums of two to eight lines and
/// `if`s over domains with holes, unbounded ends and ends beyond `i64`, tested by `z OP c`,
/// `z + x1 >= c`, or two names at once, in sequences that narrow the domains as a walk does,
/// each tree after the first found from the last by the inputs that changed
/// ([`images::updated`]); with summaries over one input, read as inputs, inputs of empty
/// domains, as in a scope no state reaches, and an input the test reads over another domain
/// than the tree's. Item PA-letpre-linear.
#[test]
fn random_tests_through_term_bounds_narrow_as_reading_every_input_does() {
    let mut rng = Rng::new(0x1e7_b0d5);
    let mut compared = 0;
    let mut narrowed = 0;
    let (mut single, mut void, mut shadowed) = (0, 0, 0);
    for round in 0..800 {
        let k = 1 + rng.below(8);
        let xs: Vec<Arc<str>> = (1..=k).map(|i| format!("x{i}").into()).collect();
        let mut names: images::Names<IntervalSet> = xs
            .iter()
            .map(|x| (x.clone(), random_domain(&mut rng)))
            .collect();
        let doms: Domains = names.iter().map(|(x, d)| (x.clone(), d.clone())).collect();
        let (z, w): (Arc<str>, Arc<str>) = ("z".into(), "w".into());
        let Some(sz) = random_sum(&mut rng, &xs, &doms) else {
            continue;
        };
        let some: Vec<Arc<str>> = xs.iter().filter(|_| rng.below(2) == 0).cloned().collect();
        let sw = if !some.is_empty() {
            random_sum(&mut rng, &some, &doms)
        } else {
            None
        };
        let lit = |v: i64| Term::Lit(Value::Int(v));
        let mut last: Vec<Option<(images::Names<IntervalSet>, images::Tree<_>)>> = vec![None, None];
        for step in 0..4 {
            // An input of no value, as in a scope no state reaches.
            if rng.below(12) == 0 {
                names.insert(rng.pick(&xs), IntervalSet::empty());
            }
            let cmp = |rng: &mut Rng, t: Term| {
                let op = rng.pick(&[Prim::Eq, Prim::Ne, Prim::Lt, Prim::Le, Prim::Gt, Prim::Ge]);
                Term::Prim(op, vec![t, lit(rng.int(-30, 30))])
            };
            let (test, own): (Term, Vec<Arc<str>>) = match (rng.below(3), &sw) {
                (1, _) => {
                    let t = Term::Prim(
                        Prim::Add,
                        vec![Term::Var(z.clone()), Term::Var(xs[0].clone())],
                    );
                    (
                        Term::Prim(Prim::Ge, vec![t, lit(rng.int(-30, 30))]),
                        vec![xs[0].clone()],
                    )
                }
                (2, Some(_)) => {
                    let a = cmp(&mut rng, Term::Var(z.clone()));
                    let b = cmp(&mut rng, Term::Var(w.clone()));
                    (Term::Prim(Prim::And, vec![a, b]), vec![])
                }
                _ => (cmp(&mut rng, Term::Var(z.clone())), vec![]),
            };
            let demand = Demand::Bool(rng.below(2) == 0);
            let ints = if rng.below(4) == 0 {
                random_domain(&mut rng)
            } else {
                IntervalSet::top()
            };
            let lets_of = |reads: Option<[Arc<TermRead<IntervalSet>>; 2]>| {
                let mut lets = Lets::new();
                let mut add = |n: &Arc<str>, s: &LetPa, i: usize| {
                    // A summary over one input reads it as an input.
                    let read = (reads.as_ref())
                        .filter(|_| s.vars().len() > 1)
                        .map(|r| r[i].clone() as _);
                    let l = LetIn {
                        summary: s.clone(),
                        ints: ints.clone(),
                        read,
                    };
                    lets.insert(n.clone(), l);
                };
                add(&z, &sz, 0);
                if let Some(sw) = &sw {
                    add(&w, sw, 1);
                }
                lets
            };
            // Each summary's tree, from the last one's where there is one.
            let reads = [Some(&sz), sw.as_ref()].map(|s| {
                let s = s.unwrap_or(&sz);
                let leaf = |v: &Arc<str>, d: &IntervalSet| s.term_bounds(v, d);
                (s, leaf)
            });
            let mut trees = Vec::new();
            for (i, (s, leaf)) in reads.iter().enumerate() {
                let tree = (last[i].as_ref())
                    .and_then(|(n, t)| {
                        let changed = images::changed(n, &names);
                        images::updated(t, changed, s.vars(), &names, s.vars().len(), leaf)
                    })
                    .unwrap_or_else(|| images::fresh(s.vars(), &names, leaf));
                last[i] = Some((names.clone(), tree.clone()));
                trees.push(Arc::new(TermRead {
                    names: names.clone(),
                    vars: s.vars().clone(),
                    tree,
                    ints: |d: &IntervalSet| d,
                }));
            }
            let reads = [trees[0].clone(), trees[1].clone()];
            // The inputs a walk gives: the test's own, and those its summaries read.
            let read = sz
                .vars()
                .iter()
                .chain(sw.iter().flat_map(|s| s.vars().iter()));
            let mut all: Domains = (own.iter().chain(read))
                .map(|x| (x.clone(), names[x].clone()))
                .collect();
            let one = ([Some(&sz), sw.as_ref()].into_iter().flatten())
                .filter(|s| s.vars().len() == 1)
                .flat_map(|s| s.vars().iter());
            let mut over: Domains = (own.iter().chain(one))
                .map(|x| (x.clone(), names[x].clone()))
                .collect();
            // An input the test reads over another domain than the scope's, within the one its
            // summaries were formed over, where they hold.
            let vars: Vec<Arc<str>> = sz.vars().iter().cloned().collect();
            if !vars.is_empty() && rng.below(3) == 0 {
                let x = rng.pick(&vars);
                let d = names[&x].meet(&random_domain(&mut rng));
                all.insert(x.clone(), d.clone());
                over.insert(x, d);
                shadowed += 1;
            }
            let want = let_preimage(&test, &all, lets_of(None), &demand);
            let got = let_narrowing(&test, &over, lets_of(Some(reads.clone())), &demand);
            let whole = let_preimage(&test, &over, lets_of(Some(reads)), &demand);
            let rebuilt: Domains = match &got {
                None => all
                    .keys()
                    .map(|x| (x.clone(), IntervalSet::empty()))
                    .collect(),
                Some(m) => {
                    assert!(
                        m.keys().all(|x| all.contains_key(x)),
                        "round {round}: {m:?}"
                    );
                    let of = |x: &Arc<str>| m.get(x).unwrap_or(&all[x]).clone();
                    all.keys().map(|x| (x.clone(), of(x))).collect()
                }
            };
            let case = format!("round {round} step {step}: {test} demand {demand:?} over {all:?}");
            assert_eq!(rebuilt, want, "{case}");
            assert_eq!(whole, want, "{case}");
            compared += 1;
            single += usize::from(
                sz.vars().len() == 1 || sw.as_ref().is_some_and(|s| s.vars().len() == 1),
            );
            void += usize::from(all.values().any(IntervalSet::is_empty));
            if want.values().any(IntervalSet::is_empty) {
                break;
            }
            if want != all {
                narrowed += 1;
            }
            for (x, d) in want {
                names.insert(x, d);
            }
        }
    }
    assert!(
        compared > 1_000 && narrowed > 300 && single > 100 && void > 20 && shadowed > 200,
        "{compared} compared, {narrowed} narrowed, {single} over one input, {void} empty, \
         {shadowed} read over another domain"
    );
}

mod bench;
