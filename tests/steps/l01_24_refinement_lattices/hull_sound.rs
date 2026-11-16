//! Row TEST-range-hull-sound: every hull a printed signature carries holds every int the
//! function gives. A function of ranged parameters prints the hull of its result
//! (`f(x: int[0..=9]) = x + 1` is `(x: int[0..=9]) -> int[1..=10]`, DESIGN.md L1.25, row
//! RANGE-result-hull), and a call of it and a fit of it where a function is wanted
//! (`fits_sig`) read that hull: a hull that misses an int the function gives lets a call
//! through that should be refused. Each test here runs the function at every point of its
//! parameters' ranges and checks each value against the printed hull; where the read is exact,
//! that both ends are reached.

use zed_tests::instances::Rng;
use zed_tests::step_helpers::l01_16_elaboration::value;
use zed_tests::step_helpers::l01_26_type_resolution::{sig_of, type_errors};

/// A function of the program under test: its name and its parameters, each with the least and
/// the greatest int of its range.
struct Fun {
    name: String,
    params: Vec<(String, i64, i64)>,
}

impl Fun {
    /// Each call of it at a point of its parameters' ranges, with the point.
    fn calls(&self) -> Vec<(String, Vec<i64>)> {
        let mut points: Vec<Vec<i64>> = vec![Vec::new()];
        for &(_, lo, hi) in &self.params {
            points = points
                .into_iter()
                .flat_map(|p| {
                    (lo..=hi).map(move |v| {
                        let mut q = p.clone();
                        q.push(v);
                        q
                    })
                })
                .collect();
        }
        points
            .into_iter()
            .map(|p| {
                let args: Vec<String> = (self.params.iter().zip(&p))
                    .map(|((n, _, _), v)| format!("{n}: {v}"))
                    .collect();
                (format!("{}({})", self.name, args.join(", ")), p)
            })
            .collect()
    }
}

/// The ints the tuple `printed` holds, as the evaluator prints it, or the printed value of the
/// first component that is no int.
fn ints_of(printed: &str) -> Result<Vec<i128>, String> {
    let inner = printed
        .strip_prefix('(')
        .and_then(|s| s.strip_suffix(')'))
        .ok_or_else(|| printed.to_string())?;
    inner
        .split(", ")
        .map(|s| s.parse::<i128>().map_err(|_| s.to_string()))
        .collect()
}

/// The least and the greatest int of the hull a function prints, each none where it is open;
/// none where it prints no hull.
type Hull = Option<(Option<i128>, Option<i128>)>;

/// What a function's signature says of its result ints, and the ints it gives.
struct Seen {
    name: String,
    /// The hull it prints, its signature's `hull`.
    hull: Hull,
    /// The ints its result type lists, where it prints one or more int literals joined by `|`
    /// (`-> 2`, `-> -3 | -1`): the checker's other way of printing a range of the result.
    listed: Option<Vec<i128>>,
    /// The int it gives at each point of its domain.
    vals: Vec<(Vec<i64>, i128)>,
}

/// The hull the function `f` of `text` prints, and the ints its printed result lists.
fn printed_range(text: &str, f: &str) -> (Hull, Option<Vec<i128>>) {
    fn end<T: std::fmt::Display>(v: &Option<T>, f: &str) -> Option<i128> {
        v.as_ref().map(|v| {
            v.to_string()
                .parse::<i128>()
                .unwrap_or_else(|_| panic!("the hull end `{v}` of `{f}` is no int"))
        })
    }
    let sig = sig_of(text, f);
    let hull = sig.hull.as_ref().map(|h| (end(&h.low, f), end(&h.high, f)));
    let shown = sig.to_string();
    let listed = shown.rsplit_once(" -> ").and_then(|(_, r)| {
        r.split(" | ")
            .map(|s| s.parse::<i128>().ok())
            .collect::<Option<Vec<_>>>()
    });
    (hull, listed)
}

/// What one program shows: for each of its functions, what it prints and what it gives.
struct Run {
    text: String,
    funs: Vec<Seen>,
}

/// Checks the program `text`, which defines `funs`, and runs each function at each point of its
/// domain: the program must be accepted, and each function must give an int at every point.
fn run(text: &str, funs: &[Fun]) -> Run {
    let errors = type_errors(text);
    assert!(errors.is_empty(), "{text}\nrejected: {errors:#?}");
    let calls: Vec<Vec<(String, Vec<i64>)>> = funs.iter().map(Fun::calls).collect();
    // One tuple of every call, and a 0 last, so that a tuple of one call is still a tuple.
    let all: Vec<&str> = calls.iter().flatten().map(|(c, _)| c.as_str()).collect();
    let program = format!("{text}hullSoundCalls = ({}, 0);\n", all.join(", "));
    let printed = value(&program, "hullSoundCalls");
    let mut ints = ints_of(&printed)
        .unwrap_or_else(|v| panic!("{program}\na call gives `{v}`, no int: {printed}"))
        .into_iter();
    let funs = (funs.iter().zip(calls))
        .map(|(f, cs)| {
            let vals = cs
                .into_iter()
                .map(|(_, p)| (p, ints.next().expect("one int per call")))
                .collect();
            let (hull, listed) = printed_range(text, &f.name);
            Seen {
                name: f.name.clone(),
                hull,
                listed,
                vals,
            }
        })
        .collect();
    Run {
        text: text.to_string(),
        funs,
    }
}

impl Run {
    /// Asserts each int each function gives lies in the hull it prints and among the ints its
    /// result lists.
    fn sound(&self) {
        for f in &self.funs {
            for (p, v) in &f.vals {
                if let Some((lo, hi)) = f.hull {
                    assert!(
                        lo.is_none_or(|lo| lo <= *v) && hi.is_none_or(|hi| *v <= hi),
                        "{}\n`{}` at {p:?} gives {v}, outside its printed hull {lo:?}..={hi:?}",
                        self.text,
                        f.name
                    );
                }
                if let Some(listed) = &f.listed {
                    assert!(
                        listed.contains(v),
                        "{}\n`{}` at {p:?} gives {v}, not among its printed result {listed:?}",
                        self.text,
                        f.name
                    );
                }
            }
        }
    }

    /// Asserts each function prints a hull, closed at both ends, whose least and greatest ints
    /// it gives.
    fn exact(&self) {
        self.sound();
        for f in &self.funs {
            let vs: Vec<i128> = f.vals.iter().map(|(_, v)| *v).collect();
            let (lo, hi) = (vs.iter().min(), vs.iter().max());
            assert_eq!(
                f.hull,
                Some((lo.copied(), hi.copied())),
                "{}\n`{}` gives ints from {lo:?} through {hi:?}",
                self.text,
                f.name
            );
        }
    }

    /// How many functions print a hull.
    fn hulls(&self) -> usize {
        self.funs.iter().filter(|f| f.hull.is_some()).count()
    }
}

/// The names of parameters.
const NAMES: [&str; 3] = ["u", "v", "w"];

/// A random range of a parameter: from -4 through 3, of 1 to 5 ints, so that its ints take
/// each sign, 0 alone, or one sign only.
fn range(rng: &mut Rng) -> (i64, i64) {
    let lo = rng.int(-4, 3);
    (lo, lo + rng.int(0, 4))
}

/// The parameters `name: int[lo..=hi]` of a function, written.
fn written(params: &[(String, i64, i64)]) -> String {
    let ps: Vec<String> = params
        .iter()
        .map(|(n, lo, hi)| format!("{n}: int[{lo}..={hi}]"))
        .collect();
    ps.join(", ")
}

/// The context of a random body: the ranged parameters, the other names it may read, the
/// ranged functions it may call, and a count for fresh names.
struct Ctx {
    params: Vec<(String, i64, i64)>,
    names: Vec<String>,
    helpers: Vec<(String, i64, i64)>,
    fresh: usize,
}

/// A random int expression of depth at most `depth` over `cx`, each operand in parentheses.
/// It reads each operator [`Ck::known`] reads: literals, parameters, names bound to values
/// (at the top level and in blocks), `-`, `+`, `-`, `*`, `div`, `mod`, `^` at a constant and
/// at a varying exponent, `x * x`, `if`, blocks, calls of ranged functions, and the bit words
/// `bitAnd`, `bitOr`, `bitXor`, `popCount`, `shl` and `shr`. Every divisor is shown nonzero,
/// every exponent at least 0 and every argument inside its range, as the checker needs; each
/// such operand is itself random, through `mod`, so the operators meet operands of each sign.
fn expr(rng: &mut Rng, cx: &mut Ctx, depth: usize) -> String {
    let leaf = |rng: &mut Rng, cx: &Ctx| match rng.below(3) {
        0 => rng.int(-3, 3).to_string(),
        _ => {
            let mut all: Vec<&String> = cx.params.iter().map(|p| &p.0).collect();
            all.extend(&cx.names);
            rng.pick(&all).clone()
        }
    };
    if depth == 0 {
        return leaf(rng, cx);
    }
    let d = depth - 1;
    let param = |rng: &mut Rng, cx: &Ctx| rng.pick(&cx.params);
    match rng.below(15) {
        0 => leaf(rng, cx),
        1 => format!("-({})", expr(rng, cx, d)),
        2..=4 => {
            let op = rng.pick(&["+", "-", "*"]);
            format!("({}) {op} ({})", expr(rng, cx, d), expr(rng, cx, d))
        }
        5 | 6 => {
            let op = rng.pick(&["div", "mod"]);
            let x = expr(rng, cx, d);
            format!("({x}) {op} ({})", divisor(rng, cx, d))
        }
        7 => format!("({}) ^ {}", expr(rng, cx, d), rng.int(0, 3)),
        8 => {
            // A varying exponent, at least 0 through `mod`, on a base of either sign or at least
            // 0 (a base that may be below 0 reads as any int).
            let base = match rng.below(2) {
                0 => expr(rng, cx, d),
                _ => format!("({}) mod 4", expr(rng, cx, d)),
            };
            format!("({base}) ^ (({}) mod 3)", expr(rng, cx, d))
        }
        9 => {
            let p = param(rng, cx).0;
            format!("{p} * {p}")
        }
        10 => {
            let p = param(rng, cx).0;
            let c = rng.int(-3, 3);
            let (a, b) = (expr(rng, cx, d), expr(rng, cx, d));
            format!("if {p} > {c} {{ {a} }} else {{ {b} }}")
        }
        11 => {
            // A block that binds a name and returns a value reading it, its square among them.
            let t = format!("t{}", cx.fresh);
            cx.fresh += 1;
            let bound = expr(rng, cx, d);
            cx.names.push(t.clone());
            let last = match rng.below(3) {
                0 => format!("{t} * {t}"),
                _ => expr(rng, cx, d),
            };
            cx.names.pop();
            format!("{{ {t} = {bound}; {last} }}")
        }
        12 if !cx.helpers.is_empty() => {
            let (g, lo, hi) = rng.pick(&cx.helpers);
            format!(
                "{g}(x: ({}) mod {} + ({lo}))",
                expr(rng, cx, d),
                hi - lo + 1
            )
        }
        13 => {
            let w = rng.pick(&["bitAnd", "bitOr", "bitXor"]);
            let (a, b) = (expr(rng, cx, d), expr(rng, cx, d));
            format!("{w}(({a}) mod 8, ({b}) mod 8)")
        }
        14 => match rng.below(2) {
            0 => format!("popCount(({}) mod 16)", expr(rng, cx, d)),
            _ => {
                let w = rng.pick(&["shl", "shr"]);
                let (x, k) = (expr(rng, cx, d), expr(rng, cx, d));
                format!("{w}({x}, ({k}) mod 3)")
            }
        },
        _ => leaf(rng, cx),
    }
}

/// A random divisor the checker shows nonzero: a nonzero literal, a parameter whose range
/// leaves out 0, or a random expression moved by `mod` into `1..=n` or `-n..=-1`.
fn divisor(rng: &mut Rng, cx: &mut Ctx, depth: usize) -> String {
    let nonzero: Vec<String> = (cx.params.iter())
        .filter(|(_, lo, hi)| *lo > 0 || *hi < 0)
        .map(|p| p.0.clone())
        .collect();
    match rng.below(4) {
        0 => rng.pick(&[-3, -2, -1, 1, 2, 3]).to_string(),
        1 if !nonzero.is_empty() => rng.pick(&nonzero),
        2 => format!("({}) mod {} + 1", expr(rng, cx, depth), rng.int(1, 4)),
        _ => format!("-(({}) mod {} + 1)", expr(rng, cx, depth), rng.int(1, 4)),
    }
}

/// A random program: a constant `k`, up to two ranged helpers `g<i>(x: int[..])`, each body
/// able to call the ones before it, and `f` of one or two ranged parameters calling any.
fn program(rng: &mut Rng) -> (String, Vec<Fun>) {
    let k = rng.int(-3, 3);
    let mut text = format!("k = {k};\n");
    let mut funs = Vec::new();
    let mut helpers = Vec::new();
    for i in 0..rng.below(3) {
        let (lo, hi) = range(rng);
        let params = vec![("x".to_string(), lo, hi)];
        let mut cx = Ctx {
            params: params.clone(),
            names: vec!["k".into()],
            helpers: helpers.clone(),
            fresh: 0,
        };
        let depth = rng.below(4);
        let body = expr(rng, &mut cx, depth);
        let g = format!("g{i}");
        text.push_str(&format!("{g}({}) = {body};\n", written(&params)));
        helpers.push((g.clone(), lo, hi));
        funs.push(Fun { name: g, params });
    }
    let params: Vec<(String, i64, i64)> = (0..1 + rng.below(2))
        .map(|i| {
            let (lo, hi) = range(rng);
            (NAMES[i].to_string(), lo, hi)
        })
        .collect();
    let mut cx = Ctx {
        params: params.clone(),
        names: vec!["k".into()],
        helpers,
        fresh: 0,
    };
    let depth = 1 + rng.below(4);
    let body = expr(rng, &mut cx, depth);
    text.push_str(&format!("f({}) = {body};\n", written(&params)));
    funs.push(Fun {
        name: "f".into(),
        params,
    });
    (text, funs)
}

/// The random programs: a new family each run (author P169), its seed printed, so that
/// `ZED_TEST_SEED=<seed>` repeats it. A failure prints the program.
#[test]
fn every_int_a_random_function_gives_lies_in_its_printed_hull() {
    let (mut rng, _) = Rng::fresh("hull_sound");
    for _ in 0..60 {
        let (text, funs) = program(&mut rng);
        run(&text, &funs).sound();
    }
}

/// A random expression of the read's exact part over the parameters `ps`, each read once:
/// a parameter, its square `x * x`, a constant power of it, or a literal, joined by `+`, `-`
/// and `*` and negated. Its ints at the ends of the hull are reached: by induction, each
/// operand's least and greatest ints are reached, the operands read disjoint parameters, so
/// any pair of their ints is reached together, and `+`, `-` and `*` take their extremes at
/// pairs of the operands' extremes (`*` is bilinear); `x * x` and `x ^ n` of one parameter
/// take theirs at its ends or at 0, which a range holding ints of both signs holds.
fn exact_expr(rng: &mut Rng, ps: &[String]) -> String {
    if ps.is_empty() {
        return rng.int(-3, 3).to_string();
    }
    if ps.len() == 1 {
        let p = &ps[0];
        let e = match rng.below(4) {
            0 => format!("{p} * {p}"),
            1 => format!("{p} ^ {}", rng.int(0, 3)),
            _ => p.clone(),
        };
        return match rng.below(4) {
            0 => format!("-({e})"),
            _ => e,
        };
    }
    let cut = 1 + rng.below(ps.len() - 1);
    let (a, b) = (exact_expr(rng, &ps[..cut]), exact_expr(rng, &ps[cut..]));
    let op = rng.pick(&["+", "-", "*"]);
    format!("({a}) {op} ({b})")
}

/// Where the read is exact, the hull's ends are the least and the greatest int the function
/// gives.
#[test]
fn the_hull_of_a_sum_or_product_of_parameters_read_once_is_reached_at_both_ends() {
    let (mut rng, _) = Rng::fresh("hull_exact");
    for _ in 0..40 {
        let n = 1 + rng.below(3);
        let params: Vec<(String, i64, i64)> = (0..n)
            .map(|i| {
                let (lo, hi) = range(&mut rng);
                (NAMES[i].to_string(), lo, hi)
            })
            .collect();
        let names: Vec<String> = params.iter().map(|p| p.0.clone()).collect();
        let body = exact_expr(&mut rng, &names);
        let text = format!("f({}) = {body};\n", written(&params));
        run(
            &text,
            &[Fun {
                name: "f".into(),
                params,
            }],
        )
        .exact();
    }
}

/// One function `f`, of the parameters `params`, in the program `text`.
fn one(text: &str, params: &[(&str, i64, i64)]) -> Run {
    let params = params
        .iter()
        .map(|&(n, lo, hi)| (n.to_string(), lo, hi))
        .collect();
    run(
        text,
        &[Fun {
            name: "f".into(),
            params,
        }],
    )
}

/// Division and remainder are Euclidean (the kernel's `div_euclid` and `rem_euclid`): the
/// remainder is never below 0, and the quotient rounds toward -infinity for a positive divisor
/// and toward +infinity for a negative one. Each sign of each operand.
#[test]
fn div_and_mod_hulls_hold_every_sign_of_each_operand() {
    for (x, y) in [
        ((-7, 7), (1, 3)),
        ((-7, 7), (-3, -1)),
        ((-7, -1), (-3, -1)),
        ((0, 7), (2, 2)),
    ] {
        for op in ["div", "mod"] {
            let text = format!(
                "f(a: int[{}..={}], b: int[{}..={}]) = a {op} b;\n",
                x.0, x.1, y.0, y.1
            );
            let r = one(&text, &[("a", x.0, x.1), ("b", y.0, y.1)]);
            r.sound();
            assert_eq!(r.hulls(), 1, "{text}");
        }
    }
    // A constant divisor shifts a piece that does not wrap: `x mod 5` of `x: int[6..=8]`.
    one("f(a: int[6..=8]) = a mod 5;\n", &[("a", 6, 8)]).exact();
    one("f(a: int[-8..=-6]) = a mod 5;\n", &[("a", -8, -6)]).exact();
    one("f(a: int[-2..=2]) = a mod -5;\n", &[("a", -2, 2)]).sound();
}

/// A range of one int, and the parameter alone, negated and squared.
#[test]
fn a_one_point_range_gives_its_one_value() {
    one("f(a: int[3..=3]) = a;\n", &[("a", 3, 3)]).exact();
    one("f(a: int[-2..=-2]) = -a * 5 + a * a;\n", &[("a", -2, -2)]).exact();
    one("f(a: int[0..=0]) = a ^ 0;\n", &[("a", 0, 0)]).exact();
}

/// A range that holds no int is an error, so no hull is printed from it.
#[test]
fn an_empty_range_is_rejected_and_prints_no_hull() {
    for text in ["f(a: int[5..=4]) = a;\n", "f(a: int[5..<5]) = a + 1;\n"] {
        assert!(!type_errors(text).is_empty(), "{text}");
    }
}

/// A call reads the hull of the function it calls, through a chain, a branch and a block.
#[test]
fn calls_of_ranged_functions_read_the_hulls_they_call() {
    let text = "g(x: int[-2..=3]) = x * x - 4;\n\
                h(x: int[-5..=5]) = g(x: x mod 6 - 2) * 2 + 1;\n\
                f(a: int[-3..=3]) = if a > 0 { h(x: a) } else { { t = g(x: a + 1); t div 2 } };\n";
    let r = run(
        text,
        &[
            Fun {
                name: "g".into(),
                params: vec![("x".into(), -2, 3)],
            },
            Fun {
                name: "h".into(),
                params: vec![("x".into(), -5, 5)],
            },
            Fun {
                name: "f".into(),
                params: vec![("a".into(), -3, 3)],
            },
        ],
    );
    r.sound();
    assert_eq!(r.hulls(), 3, "{text}");
}

/// A name bound to one of two functions by a branch holds both at its call: the hull `f` prints
/// holds the results of each, whether their hulls are apart, one inside the other either way
/// round, or equal.
#[test]
fn a_call_of_a_name_bound_to_either_of_two_functions_holds_both_results() {
    for (g1, g2) in [
        ("x", "x + 10"),
        ("x", "x * 2"),
        ("x * 2", "x"),
        ("x", "3 - x"),
    ] {
        for h in [
            "if b == 0 { g1 } else { g2 }",
            "if b > 0 { g1 } else { g2 }",
        ] {
            let text = format!(
                "g1(x: int[0..=3]) = {g1};\ng2(x: int[0..=3]) = {g2};\n\
                 f(a: int[0..=3], b: int[0..=1]) = {{ h = {h}; h(x: a) }};\n"
            );
            one(&text, &[("a", 0, 3), ("b", 0, 1)]).sound();
        }
    }
}

/// A call that leaves out a parameter gives it its default, so a default outside the range
/// would give `g` a value outside its printed hull `int[0..=3]`: the call is refused. (A
/// default inside the range is refused too, which is row RANGE-default-in-range.)
#[test]
fn a_default_outside_the_range_is_not_read_as_inside_it() {
    let text = "g(x: int[0..=3] = 10) = x;\nf(a: int[0..=1]) = g() + a;\n";
    let errors = type_errors(text);
    assert!(
        errors.iter().any(|e| e.contains("`g()` leaves out `x`")),
        "{text}\n{errors:#?}"
    );
}
