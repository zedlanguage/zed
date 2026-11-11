//! The Trick's general arm and the staging corners (test audit 2026-11-08, row 5). A split
//! function computes what the function does on every value: on the values its static calls
//! pass, on the other values of the domain, on values outside it, and on a value the program
//! reads from a port at run time. A binding whose evaluation stops is evaluated once, however
//! many definitions read it, and a binding or definition named only in a branch the build cuts
//! is still evaluated. The Trick splits on tuple and finite literal set domains and never on a
//! function domain.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use zed_kernel::types::Type;
use zed_kernel::{Evaluator, Lookup, Pattern, Shared, Term, Value, World};
use zed_tests::instances::{RANDOM_INSTANCES, Rng};
use zed_tests::scaling::Meter;
use zed_tests::step_helpers::l01_16_elaboration::{elab, with_prelude};
use zedc::elab::Unit;
use zedc::run::{Program, direct, load};
use zedc::stage::{Choice, Domain, passed, split, trick};

use super::{out, staged, term};

/// The seed of every random input here, printed with each failure.
const SEED: u64 = 0x0128_7a11;

/// A shop: the tier decides the rate and the zone the shipping, as in `trick.rs`.
const SHOP: &str = "rate = 8;\n\
    price(tier, n: int) = if tier == #gold { n * rate } else { n * (rate + 2) };\n\
    ship(zone: int, kg: int) = if zone == 0 { kg } else { kg * zone + rate };\n\
    order(m: int) = price(tier: #gold, n: m) + price(tier: #basic, n: m) + ship(zone: 0, kg: m) + ship(zone: 3, kg: m);\n";

/// `u` with the term of its definition `name` replaced by `t`.
fn with_def(u: &Unit, name: &str, t: Term) -> Unit {
    let mut changed = u.clone();
    let d = changed.defs.iter_mut().find(|d| d.name == name);
    d.unwrap_or_else(|| panic!("no definition `{name}`")).term = Shared::new(t);
    changed
}

/// The definition `name` of `u` called on `args`, run under the prelude: its value or the
/// evaluator's error.
fn call(u: &Unit, name: &str, args: &[Value]) -> Result<Value, String> {
    let f = u
        .get(name)
        .unwrap_or_else(|| panic!("no definition `{name}`"));
    let args = args.iter().cloned().map(Term::Lit).collect();
    let t = Term::App(Shared::new(f), args);
    let mut ev = Evaluator::new(World::new());
    ev.run(&with_prelude(t)).map_err(|e| e.to_string())
}

/// The values a split function's arms list, in order; its last arm is the general one.
fn listed(lam: &Term) -> Vec<Value> {
    let Term::Lam(_, body) = lam else {
        panic!("a split function is a lambda: {lam}")
    };
    let Term::Match(_, arms) = &**body else {
        panic!("its body is a match: {lam}")
    };
    assert!(matches!(arms.last(), Some((Pattern::Wild, _))), "{lam}");
    arms.iter()
        .filter_map(|(p, _)| match p {
            Pattern::Lit(v) => Some(v.clone()),
            _ => None,
        })
        .collect()
}

/// Splits `name` of `u` on `param` over `d`, checks that the split function gives what the
/// function as written gives on each of `inputs`, value or error, and that the inputs take
/// each arm, the general one too. The split function's text is returned.
fn agree(u: &Unit, name: &str, param: usize, d: &Domain, inputs: &[Vec<Value>]) -> String {
    let (lam, report) = split(u, name, param, d).unwrap_or_else(|e| panic!("{name}: {e}"));
    assert!(report.left.is_empty(), "{name}: {:?}", report.left);
    let listed = listed(&lam);
    let staged = with_def(u, name, lam.clone());
    let mut taken: BTreeSet<Option<&Value>> = BTreeSet::new();
    for args in inputs {
        taken.insert(listed.iter().find(|v| **v == args[param]));
        assert_eq!(
            call(&staged, name, args),
            call(u, name, args),
            "{name} at {args:?}, seed {SEED:#x}: the split function {lam}"
        );
    }
    assert_eq!(
        taken.len(),
        listed.len() + 1,
        "{name}: arms taken {taken:?}"
    );
    lam.to_string()
}

/// The tiers to try: the two the calls pass, `#silver`, which the domain does not hold, and
/// values of other kinds.
fn tiers() -> Vec<Value> {
    vec![
        Value::atom("gold"),
        Value::atom("basic"),
        Value::atom("silver"),
        Value::atom_with("gold", vec![Value::Int(1)]),
        Value::Int(0),
        Value::Bool(true),
        Value::str("gold"),
    ]
}

/// Integers to try: `-3..=12`, the ends of a machine word and numbers near them, and random
/// numbers, small and of any size a machine word holds.
fn numbers(rng: &mut Rng) -> Vec<i64> {
    let mut ns: Vec<i64> = (-3..=12).collect();
    ns.extend([
        i64::MIN,
        i64::MIN + 1,
        -(1 << 40),
        1 << 40,
        i64::MAX - 1,
        i64::MAX,
    ]);
    ns.extend((0..RANDOM_INSTANCES).map(|_| rng.int(-1_000_000, 1_000_000)));
    ns.extend((0..RANDOM_INSTANCES).map(|_| rng.next_u64() as i64));
    ns
}

/// The tests of `trick.rs` compare the split functions with the functions only at the values
/// the calls pass, `#gold` and `#basic`, so the general arm was never run. Here every tier,
/// `#silver` and values of other kinds among them, and every zone, the domain's `1, 2, 4..=9`
/// and those outside it among them, with random numbers.
#[test]
fn a_split_function_gives_what_the_function_gives_on_every_value() {
    let u = elab(SHOP).unwrap();
    let mut rng = Rng::new(SEED);
    let ns = numbers(&mut rng);
    let tiers_domain = Domain::Type(&Type::atom("gold") | &Type::atom("basic"));
    let mut inputs: Vec<Vec<Value>> = Vec::new();
    for t in tiers() {
        for n in [0, 1, -7, 1 << 40, i64::MAX] {
            inputs.push(vec![t.clone(), Value::Int(n)]);
        }
    }
    for &n in &ns {
        inputs.push(vec![rng.pick(&tiers()), Value::Int(n)]);
    }
    assert_eq!(
        agree(&u, "price", 0, &tiers_domain, &inputs),
        "(tier, n) -> match tier { #basic -> (n * 10), #gold -> (n * 8), _ -> if (tier == \
         #gold) { (n * 8) } else { (n * 10) } }"
    );
    let zones = Domain::Ints(Some(0), Some(9));
    let mut inputs: Vec<Vec<Value>> = Vec::new();
    for &z in &ns {
        for _ in 0..4 {
            inputs.push(vec![Value::Int(z), Value::Int(rng.pick(&ns))]);
        }
    }
    agree(&u, "ship", 0, &zones, &inputs);
}

/// A shop whose zone is read from the input at run time. The calls that pass a literal zone
/// pass a weight read from the input too, so the build leaves them to run and they are the
/// static calls the Trick reads.
const PORT: &str = "rate = 8;\n\
    ship(zone: int, kg: int) = if zone == 0 { kg } else { kg * zone + rate };\n\
    main(m: MainArgs) {\n  \
    z = int(m.stdin[1]) else 0;\n  \
    m.stdout <- String(ship(zone: 0, kg: z) + ship(zone: 3, kg: z) + ship(zone: z, kg: 7));\n}\n";

/// What `main` of `p`, closed over `u` in place of `p`'s unit, writes on `stdin`.
fn out_with(p: &Program, u: &Unit, stdin: &str) -> String {
    let lines: BTreeMap<String, Arc<[u8]>> = p
        .inputs()
        .iter()
        .map(|(name, _)| (name.clone(), Arc::from(stdin.as_bytes())))
        .collect();
    let files = |_: &str| -> Arc<dyn Lookup> { unreachable!("no `Files` port") };
    let main = u.get("main").expect("`main`");
    match p.run_main_through(&main, &lines, &[], files, &direct) {
        Ok(w) => w
            .writes
            .iter()
            .map(|(_, b)| String::from_utf8_lossy(b).into_owned())
            .collect(),
        Err(e) => format!("error: {e}"),
    }
}

#[test]
fn a_split_function_called_with_a_value_read_at_run_time_gives_what_the_function_gives() {
    let p = load(PORT.as_bytes()).unwrap();
    let u = p.unit();
    assert_eq!(passed(u, "ship", 0), [Value::Int(0), Value::Int(3)].into());
    let (lam, _) = split(u, "ship", 0, &Domain::Ints(Some(0), Some(9))).unwrap();
    assert_eq!(
        lam.to_string(),
        "(zone, kg) -> match zone { 0 -> kg, 3 -> ((kg * 3) + 8), _ -> if (zone == 0) { kg } \
         else { ((kg * zone) + 8) } }"
    );
    let changed = with_def(u, "ship", lam);
    let mut rng = Rng::new(SEED);
    let mut inputs: Vec<String> = (-3..=12).map(|z| format!("{z}\n")).collect();
    inputs.extend((0..64).map(|_| format!("{}\n", rng.int(-1_000_000, 1_000_000))));
    inputs.extend(["noise\n".into(), "\n".into()]);
    for stdin in &inputs {
        assert_eq!(
            out_with(&p, &changed, stdin),
            out(&p, stdin),
            "stdin {stdin:?}, seed {SEED:#x}"
        );
    }
    // Zone 4, which no call passes, takes the general arm in the third call: 4 + (4 * 3 + 8)
    // + (7 * 4 + 8).
    assert_eq!(out_with(&p, &changed, "4\n"), "60\n");
}

/// A program in which `readers` definitions read one binding, `huge`, whose evaluation stops.
fn stopped_read_by(readers: usize) -> String {
    let mut s = format!("{}huge = {};\n", zed_tests::TWICE, zed_tests::too_long());
    for i in 0..readers {
        s += &format!("r{i} = huge ++ \"{i}\";\n");
    }
    let all: Vec<String> = (0..readers).map(|i| format!("r{i}")).collect();
    s += &format!(
        "main(m: MainArgs) {{\n  m.stdout <- {};\n}}\n",
        all.join(" ++ ")
    );
    s
}

/// A program in which `readers` definitions each read a binding of their own whose evaluation
/// stops: `readers` evaluations that stop.
fn stopped_each(readers: usize) -> String {
    let mut s = String::from(zed_tests::TWICE);
    for i in 0..readers {
        s += &format!(
            "h{i} = {};\nr{i} = h{i} ++ \"{i}\";\n",
            zed_tests::too_long()
        );
    }
    let all: Vec<String> = (0..readers).map(|i| format!("r{i}")).collect();
    s += &format!(
        "main(m: MainArgs) {{\n  m.stdout <- {};\n}}\n",
        all.join(" ++ ")
    );
    s
}

/// The least work of staging `p` in two runs.
fn staging_work(meter: &mut Meter, p: &Program) -> u64 {
    (0..2)
        .map(|_| {
            meter
                .work(|| {
                    std::hint::black_box(p.stage());
                })
                .units
        })
        .min()
        .expect("two runs")
}

/// DESIGN step L1.28: an evaluation that stops leaves the term to run whole, and the name it
/// binds becomes run-stage, so nothing evaluates it twice. Read by two definitions, `huge` is
/// left once and its readers are left as written. The evaluations are counted by their work:
/// the stop of `huge` costs about 6.8 million instructions, and 8 readers of it cost about
/// 0.5 million more than one (measured 2026-11-11); were each reader to evaluate `huge` again,
/// 7 more readers would cost 7 stops more.
#[test]
fn a_stopped_binding_read_twice_is_evaluated_once() {
    let (p, s, report) = staged(&stopped_read_by(2));
    assert!(report.built.is_empty(), "{:?}", report.built);
    assert_eq!(report.left.len(), 1, "{:?}", report.left);
    assert_eq!(report.left[0].0.to_string(), term(&p, "huge"));
    assert!(report.left[0].1.contains("a string's length can hold"));
    for x in ["huge", "r0", "r1"] {
        assert_eq!(term(&s, x), term(&p, x), "{x}");
    }
    assert!(out(&s, "x\n").starts_with("error: `++` cannot join"));
    assert_eq!(out(&s, "x\n"), out(&p, "x\n"));
    let mut meter = Meter::new();
    let [one, eight] = [1, 8].map(|k| load(stopped_read_by(k).as_bytes()).unwrap());
    let [each_one, each_two] = [1, 2].map(|k| load(stopped_each(k).as_bytes()).unwrap());
    let (one, eight) = (
        staging_work(&mut meter, &one),
        staging_work(&mut meter, &eight),
    );
    let stop = staging_work(&mut meter, &each_two) - staging_work(&mut meter, &each_one);
    assert!(
        eight - one < stop / 2,
        "8 readers of one stopped binding cost {} {unit} more than 1 reader; one more stop costs \
         {stop}",
        eight - one,
        unit = meter.unit()
    );
}

/// DESIGN step L1.28: a local binding counts as read when its body names it, so a binding
/// named only in a branch cut later is still evaluated. `huge` is named only in the arm the
/// build cuts: the build evaluates it, the evaluation stops, and the staged program keeps the
/// binding, so its run stops as the program's does.
#[test]
fn a_binding_named_only_in_a_cut_branch_is_still_evaluated() {
    let src = format!(
        "{}main(m: MainArgs) {{\n  huge = {};\n  \
         m.stdout <- if false {{ huge }} else {{ \"x\" }};\n}}\n",
        zed_tests::TWICE,
        zed_tests::too_long()
    );
    let (p, s, report) = staged(&src);
    assert!(report.unread.is_empty(), "{:?}", report.unread);
    assert_eq!(report.left.len(), 1, "{:?}", report.left);
    assert!(report.left[0].1.contains("a string's length can hold"));
    let main = term(&s, "main");
    assert!(
        main.contains("huge = twice(") && !main.contains("if"),
        "{main}"
    );
    assert!(out(&s, "x\n").starts_with("error: `++` cannot join"));
    assert_eq!(out(&s, "x\n"), out(&p, "x\n"));
}

/// `src` with `huge`, a definition whose evaluation stops, and `verbose = false` before it.
fn with_huge(src: &str) -> String {
    format!(
        "{}verbose = false;\nhuge = {};\n{src}",
        zed_tests::TWICE,
        zed_tests::too_long()
    )
}

/// The same with `huge` a definition: `main` reads it, so it is demanded, and a run
/// evaluates every definition `main` reaches, call by value, before `main` runs (DESIGN step
/// M0.9), so the program stops. The build cuts the branch, and the staged `main` keeps a read
/// of `huge`, so its run stops as the program's does (DESIGN step L1.28: the run reports the
/// stop in the ordinary way; G7).
#[test]
fn a_definition_named_only_in_a_cut_branch_is_still_evaluated() {
    let (p, s, report) = staged(&with_huge(
        "main(m: MainArgs) {\n  m.stdout <- if verbose { huge } else { \"x\" };\n}\n",
    ));
    assert_eq!(report.left.len(), 1, "{:?}", report.left);
    let main = term(&s, "main");
    assert!(main.contains("huge") && !main.contains("if"), "{main}");
    assert!(out(&p, "x\n").starts_with("error: `++` cannot join"));
    assert_eq!(out(&s, "x\n"), out(&p, "x\n"));
    // A remix (step L25.8) mixes `main`'s term as `mix` mixes the definition, read kept.
    let written = p.unit().defs.iter().find(|d| d.name == "main").unwrap();
    let (_, mut remix) = zedc::stage::Remix::new(p.unit());
    assert_eq!(remix.mix(&written.term).to_string(), main);
}

/// The cut read is kept through a definition the build turns into a literal: `label` names
/// `huge` only in its cut branch, and `main` reads `label`, so the program stops, and so does
/// the staged one, whose `label` keeps the read.
#[test]
fn a_cut_read_is_kept_through_a_definition_built_to_a_literal() {
    let (p, s, report) = staged(&with_huge(
        "label = if verbose { huge } else { \"x\" };\n\
         main(m: MainArgs) {\n  m.stdout <- label;\n}\n",
    ));
    assert_eq!(report.left.len(), 1, "{:?}", report.left);
    assert!(term(&s, "label").contains("huge"), "{}", term(&s, "label"));
    assert!(out(&p, "x\n").starts_with("error: `++` cannot join"));
    assert_eq!(out(&s, "x\n"), out(&p, "x\n"));
}

/// The cut read is kept in a function: `shout` names `huge` only in its cut branch, and
/// `main` calls it, so the program stops, and so does the staged one, whose `shout` is still
/// a function that reads `huge`.
#[test]
fn a_cut_read_is_kept_in_a_function() {
    let (p, s, report) = staged(&with_huge(
        "shout(positional a: String) = if verbose { huge } else { a ++ \"!\" };\n\
         main(m: MainArgs) {\n  m.stdout <- shout(\"x\");\n}\n",
    ));
    assert_eq!(report.left.len(), 1, "{:?}", report.left);
    let shout = term(&s, "shout");
    assert!(shout.contains("huge") && !shout.contains("if"), "{shout}");
    assert!(out(&p, "x\n").starts_with("error: `++` cannot join"));
    assert_eq!(out(&s, "x\n"), out(&p, "x\n"));
}

/// A cut branch that names only definitions whose evaluation ends with a value keeps no read:
/// evaluating `rate` has no effect, so the staged `main` neither names it nor reads it.
#[test]
fn a_cut_read_of_a_definition_that_ends_is_not_kept() {
    let (p, s, report) = staged(
        "verbose = false;\nrate = 8;\n\
         main(m: MainArgs) {\n  m.stdout <- if verbose { String(rate) } else { \"x\" };\n}\n",
    );
    assert!(report.left.is_empty(), "{:?}", report.left);
    let main = term(&s, "main");
    assert!(!main.contains("rate") && !main.contains("$0"), "{main}");
    assert_eq!(out(&s, "x\n"), "x\n");
    assert_eq!(out(&s, "x\n"), out(&p, "x\n"));
}

/// A program of `n` definitions `s{i}` left to run, since their form does not show that they
/// end, each named by `g{i}` only in a branch the build cuts, and `main` writing every `g{i}`.
fn cut_reads(n: usize) -> String {
    let mut s = String::from("w(positional f) = f(f);\n");
    for i in 0..n {
        s += &format!("s{i} = w(w);\ng{i} = if false {{ String(s{i}) }} else {{ \"{i}\" }};\n");
    }
    let all: Vec<String> = (0..n).map(|i| format!("g{i}")).collect();
    s += &format!(
        "main(m: MainArgs) {{\n  m.stdout <- {};\n}}\n",
        all.join(" ++ ")
    );
    s
}

/// Keeping cut reads stays O(N log N) in the unit's size with many roots and many definitions
/// left to run: every `g{i}` and `main` a root, `n` definitions left, each kept by one read
/// (COMPLEXITY.md row of `keep_cut_reads`). Units are elaborated before timing.
#[test]
fn cut_reads_are_kept_in_time_that_scales() {
    let n = 600;
    let units = zed_tests::scaling::inputs(n, |k| {
        let p = load(cut_reads(k).as_bytes()).unwrap();
        let roots: Vec<String> = (0..k).map(|i| format!("g{i}")).collect();
        (p.unit().clone(), roots)
    });
    let (u, roots) = &units[&n];
    let mut all: Vec<&str> = roots.iter().map(String::as_str).collect();
    all.push("main");
    let (mixed, report) = zedc::stage::mix(u, &all);
    assert_eq!(report.left.len(), n, "{:?}", report.left);
    for i in [0, n - 1] {
        let g = mixed
            .defs
            .iter()
            .find(|d| d.name == format!("g{i}"))
            .unwrap();
        assert!(g.term.to_string().contains(&format!("s{i}")), "{}", g.term);
    }
    zed_tests::scaling::check("keeping the cut reads of n left definitions", n, |k| {
        let (u, roots) = &units[&k];
        let mut all: Vec<&str> = roots.iter().map(String::as_str).collect();
        all.push("main");
        std::hint::black_box(zedc::stage::mix(u, &all));
    });
}

/// Routes: a tuple of a bool and a bare atom, a finite domain whose four values are listed no
/// longer than they are written. One call passes a route outside it.
const ROUTES: &str = "rate = 8;\n\
    fee(route, kg: int) = if route == (true, #air) { kg * rate } else { kg + rate };\n\
    order(m: int) = fee(route: (true, #air), kg: m) + fee(route: (false, #sea), kg: m) + fee(route: (true, #rail), kg: m);\n";

#[test]
fn the_trick_splits_a_tuple_domain_on_the_tuples_passed_within_it() {
    let route = |b: bool, a: &str| Value::tuple(vec![Value::Bool(b), Value::atom(a)]);
    let ways = &Type::atom("air") | &Type::atom("sea");
    let d = Domain::Type(Type::tuple(vec![Type::bool(), ways]));
    let given: BTreeSet<Value> = [
        route(true, "air"),
        route(true, "rail"),
        Value::tuple(vec![Value::Int(1), Value::atom("air")]),
        Value::tuple(vec![Value::Bool(false), Value::atom("sea"), Value::Int(1)]),
        Value::Bool(true),
    ]
    .into();
    assert_eq!(trick(&d, &given), Choice::Split(vec![route(true, "air")]));
    // A tuple with an infinite component is kept.
    let wide = Domain::Type(Type::tuple(vec![Type::bool(), Type::int()]));
    assert_eq!(
        trick(&wide, &given),
        Choice::Keep("the domain `(bool, int)` is not known to be finite".into())
    );
    let u = elab(ROUTES).unwrap();
    assert_eq!(
        passed(&u, "fee", 0),
        [route(true, "air"), route(false, "sea"), route(true, "rail")].into()
    );
    let mut rng = Rng::new(SEED);
    let ns = numbers(&mut rng);
    let routes = [
        route(true, "air"),
        route(true, "sea"),
        route(false, "air"),
        route(false, "sea"),
        route(true, "rail"),
        Value::tuple(vec![Value::Bool(true)]),
        Value::atom("air"),
    ];
    let inputs: Vec<Vec<Value>> = (ns.iter())
        .flat_map(|&n| routes.iter().map(move |r| vec![r.clone(), Value::Int(n)]))
        .collect();
    assert_eq!(
        agree(&u, "fee", 0, &d, &inputs),
        "(route, kg) -> match route { (false, #sea) -> (kg + 8), (true, #air) -> (kg * 8), _ \
         -> if (route == (true, #air)) { (kg * 8) } else { (kg + 8) } }"
    );
}

#[test]
fn the_trick_splits_a_finite_literal_set_on_the_values_passed_within_it() {
    let set = Type::union_all([0, 3, 7].map(|i| Type::lit(&Value::Int(i)).expect("an int")));
    let d = Domain::Type(set);
    let given: BTreeSet<Value> = [0, 1, 3, 9].map(Value::Int).into();
    assert_eq!(
        trick(&d, &given),
        Choice::Split(vec![Value::Int(0), Value::Int(3)])
    );
    assert_eq!(
        trick(&d, &[Value::Int(9)].into()),
        Choice::Keep("no static call passes a value of the domain".into())
    );
    let u = elab(SHOP).unwrap();
    let mut rng = Rng::new(SEED);
    let ns = numbers(&mut rng);
    let inputs: Vec<Vec<Value>> = (ns.iter())
        .map(|&z| vec![Value::Int(z), Value::Int(rng.pick(&ns))])
        .collect();
    agree(&u, "ship", 0, &d, &inputs);
}

#[test]
fn the_trick_never_splits_a_function_domain() {
    for (t, text) in [
        (Type::exact(Type::bool(), Type::bool()), "bool -> bool"),
        (Type::exact(Type::int(), Type::int()), "int -> int"),
    ] {
        let why = format!("the domain `{text}` is not known to be finite");
        let given: BTreeSet<Value> = [Value::Bool(true), Value::Int(3)].into();
        assert_eq!(
            trick(&Domain::Type(t.clone()), &given),
            Choice::Keep(why.clone())
        );
        let src = "inc(positional v: int) = v + 1;\napply(f, x: int) = f(x);\n\
                   use(m: int) = apply(f: inc, x: m) + apply(f: inc, x: 2 * m);\n";
        let u = elab(src).unwrap();
        assert_eq!(split(&u, "apply", 0, &Domain::Type(t)).unwrap_err(), why);
    }
}
