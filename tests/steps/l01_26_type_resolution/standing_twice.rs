//! A variable of the type the checker found for a function prints as its bound where it
//! stands in one place, and as a type variable where it stands in two places or more, as the
//! printer counts the places (DESIGN.md sec:diagnostics, "Types in a message"; plan row
//! TEST-standing-twice-matches-printer).

/// The report of loading `src`, which the checker rejects.
fn report(src: &str) -> String {
    match zedc::run::load(src.as_bytes()) {
        Ok(_) => panic!("accepted:\n{src}"),
        Err(e) => e.to_string(),
    }
}

/// A function whose parameter `f` is a partial function: a value passed at `f` takes the type
/// `(x: int | f64) ->? int`.
const APPLY: &str = "apply(f: (x: int | f64) ->? int) = f(x: 2.5) else #notFound -> 6;\n";

/// The entry `e` of `xs` is passed at `f`, and stands in one place of the type of `k`: inside
/// the type of `h`, the function `k` returns. It prints as the type it is passed at, not `_`.
#[test]
fn a_variable_in_one_place_inside_a_held_function_prints_as_its_bound() {
    let src = format!(
        "{APPLY}k(xs) = {{\n  e = xs[0];\n  h(positional y) = (apply(f: e), e);\n  h\n}};\na = k(xs: [1]);\n"
    );
    let out = report(&src);
    assert!(
        out.contains(
            "the type the checker found for `k` is `(xs: _) -> _ -> (int, (x: int | f64) ->? int)`"
        ),
        "{src}\n{out}"
    );
}

/// `v` stands in the parameter and in the union `v | E` of the result, where `E`, the type of
/// the entry `xs[0]`, stands in that union only and so prints `_`. That union prints `_` alone,
/// since `_` holds every value, so `v` stands in one place of the text and prints as the type
/// it is passed at.
#[test]
fn a_variable_whose_other_place_is_a_union_printed_blank_prints_as_its_bound() {
    let src = format!(
        "{APPLY}k(v, xs, c: bool) = (apply(f: v), if c {{ v }} else {{ xs[0] }});\na = k(v: 3, xs: [1], c: true);\n"
    );
    let out = report(&src);
    assert!(
        out.contains(
            "the type the checker found for `k` is `(v: (x: int | f64) ->? int, xs: _, c: bool) -> (int, _)`"
        ),
        "{src}\n{out}"
    );
}

/// What the failed test `r is #a` leaves of `r` prints with the variable of `r` (DESIGN.md
/// sec:diagnostics: "What an `else` or a failed test leaves of a value prints with the
/// variable of that value"), so the two stand in two places and print `T`, though what is
/// left is passed at `f`.
#[test]
fn what_a_failed_test_leaves_prints_with_the_variable_of_the_value() {
    let src = format!(
        "{APPLY}k(r) = if r is #a {{ (0, 0) }} else {{ (apply(f: r), r) }};\na = k(r: 3);\n"
    );
    let out = report(&src);
    assert!(
        out.contains("the type the checker found for `k` is `(r: T) -> (0, 0) | (int, T)`"),
        "{src}\n{out}"
    );
}

/// A variable bounded by carriers is written by name with its bounds clause wherever it stands
/// (DESIGN.md sec:diagnostics, "The type of a declaration in a message"): `n`, passed at
/// `int | f64` and added, stands in two places of `k`'s type, as `n + n` gives it back, and
/// in one place of `j`'s, and is `U` in both.
#[test]
fn a_variable_bounded_by_carriers_prints_by_name_in_one_place_or_two() {
    let src = format!(
        "{APPLY}w(positional x: int | f64) = 0;\nk(v, n) = (apply(f: v), w(n), n + n);\nj(v, n) = (apply(f: v), w(n), n + 1 > 0);\na = k(v: 3, n: 1);\nb = j(v: 3, n: 1);\n"
    );
    let out = report(&src);
    for found in [
        "the type the checker found for `k` is `(v: (x: int | f64) ->? int, n: U) -> (int, 0, U) for U in int | f64`",
        "the type the checker found for `j` is `(v: (x: int | f64) ->? int, n: U) -> (int, 0, bool) for U in int | f64`",
    ] {
        assert!(out.contains(found), "{src}\n{out}");
    }
}

/// The parts a generated signature is made of, each over the variables `x` and `y`: a variable,
/// a tuple, a payload, a held function, unions with a variable and without, and none.
fn pieces() -> Vec<String> {
    let vars = ["T", "U"];
    let mut out = vec!["int".to_string()];
    for x in vars {
        out.push(x.to_string());
        out.push(format!("#a({x})"));
        out.push(format!("{x} | int"));
        for y in vars {
            out.push(format!("({x}, {y})"));
            out.push(format!("((z: {x}) -> {y})"));
            out.push(format!("{x} | {y}"));
        }
    }
    out
}

/// The type variables `s` prints by name, as its Display writes it.
pub(crate) fn printed_names(s: &zedc::check::ty::Sig) -> std::collections::BTreeSet<String> {
    let text = s.to_string();
    (text.split(|c: char| !c.is_ascii_alphanumeric() && c != '_'))
        .filter(|w| {
            let mut cs = w.chars();
            cs.next().is_some_and(|c| c.is_ascii_uppercase()) && cs.all(|c| c.is_ascii_digit())
        })
        .map(str::to_string)
        .collect()
}

/// The first signature `text` reads as.
pub(crate) fn read_sig(text: &str) -> zedc::check::ty::Sig {
    let t = zedc::check::read::parse_type(text).unwrap_or_else(|e| panic!("{text}: {e}"));
    let s = t
        .fns
        .iter()
        .next()
        .unwrap_or_else(|| panic!("{text}: no function"));
    (**s).clone()
}

/// Over generated signatures (tuples shared and not, payloads, held functions, unions, and
/// what an `else` leaves of a variable), the variables [`Sig::standing_twice`] gives are the
/// ones the printer writes by name: as many as the names in the text, counting variables an
/// `else` joins as one, and each a variable the signature binds.
#[test]
fn the_variables_standing_twice_are_the_ones_printed_by_name() {
    use std::collections::BTreeSet;
    use std::sync::Arc;
    use zedc::check::ty::{Binds, CallPath, Narrow, Need, NeedKind, Sig, Ty};
    let span = zedc::lex::Span { start: 0, end: 0 };
    // `joined`: whether an `else` on `T` gives `U`, so that the two print as one variable.
    let check = |s: &Sig, joined: bool, bad: &mut Vec<String>| {
        let twice = s.standing_twice();
        let class = |v: &Arc<str>| match (joined, &**v) {
            (true, "U") => "T".to_string(),
            _ => v.to_string(),
        };
        let classes: BTreeSet<String> = twice.iter().map(class).collect();
        let names = printed_names(s);
        let bound = twice
            .iter()
            .all(|v| s.own.contains(v) || s.bounds.contains_key(v));
        if classes.len() != names.len() || !bound {
            bad.push(format!("`{s}` joined={joined}: standing twice {twice:?}"));
        }
    };
    let with_else = |s: &Sig| {
        let mut s = s.clone();
        s.needs.push(Need {
            on: Ty::var("T".into()),
            kind: NeedKind::Narrow(Narrow::Loose),
            result: Some(Ty::var("U".into())),
            span,
            alike: Arc::from([]),
            via: CallPath::default(),
        });
        s
    };
    let pieces = pieces();
    let mut bad = Vec::new();
    let mut n = 0;
    for a in &pieces {
        for b in &pieces {
            for c in &pieces {
                let s = read_sig(&format!("(a: {a}, b: {b}) -> {c}"));
                check(&s, false, &mut bad);
                if s.own.contains("T") && s.own.contains("U") {
                    check(&with_else(&s), true, &mut bad);
                }
                n += 1;
            }
            // The tuple `(T, U)` shared: the one tuple stands at `c`, at `b` and in the
            // result, where `S` stood.
            let s = read_sig(&format!("(a: {a}, b: S, c: (T, U)) -> {b} | S"));
            let shared = s.arrows[0].params[2].clone();
            let binds: Binds = [(Arc::<str>::from("S"), shared)].into();
            let s = s.replace(&binds);
            check(&s, false, &mut bad);
            if s.own.contains("T") && s.own.contains("U") {
                check(&with_else(&s), true, &mut bad);
            }
            n += 1;
        }
    }
    assert!(
        bad.is_empty(),
        "{} of {n} signatures differ; the first:\n{}",
        bad.len(),
        bad[..bad.len().min(30)].join("\n")
    );
}

/// The places of `v` in `text`, a signature's Display, but the one its bounds clause names.
fn places_of(text: &str, v: &str) -> usize {
    let words = text.split(|c: char| !c.is_ascii_alphanumeric() && c != '_');
    let all = words.filter(|w| *w == v).count();
    all - text.matches(&format!("for {v} in ")).count()
}

/// A variable bounded by carriers, `N` of `int | f64`, is printed by name wherever it stands,
/// so [`Sig::standing_twice`] gives it exactly where the text writes it in two places or more:
/// over generated signatures holding it beside the unbounded `T`, in tuples, payloads, held
/// functions and unions, among them unions printed `_`, which hold no place of it. The
/// unbounded variables are checked as in
/// [`the_variables_standing_twice_are_the_ones_printed_by_name`]. The parts with no variable,
/// `(int, int)` and `(z: int) -> int`, alone and in unions, test the walk's skip of the tuples
/// and functions that hold no variable (`Shared::closed`, crates/zedc-types/src/ty.rs), which
/// must leave every count as the printer makes it.
#[test]
fn a_variable_bounded_by_carriers_stands_twice_where_the_text_writes_it_twice() {
    let pieces = [
        "int",
        "N",
        "T",
        "#a(N)",
        "N | int",
        "N | T",
        "(N, T)",
        "(N, N)",
        "((z: N) -> T)",
        "((z: T) -> N)",
        "(int, int)",
        "((z: int) -> int)",
        "T | (int, int)",
        "T | ((z: int) -> int)",
        "N | (int, int)",
    ];
    let mut bad = Vec::new();
    let (mut n, mut named_twice, mut named_once) = (0, 0, 0);
    for a in pieces {
        for b in pieces {
            for c in pieces {
                let arrows = format!("(a: {a}, b: {b}) -> {c}");
                let text = match arrows.contains('N') {
                    true => format!("({arrows} for N in int | f64)"),
                    false => arrows,
                };
                let s = read_sig(&text);
                let twice = s.standing_twice();
                let shown = s.to_string();
                let places = places_of(&shown, "N");
                match places {
                    0 => {}
                    1 => named_once += 1,
                    _ => named_twice += 1,
                }
                let unbounded = |v: &String| v != "N";
                let names = printed_names(&s).into_iter().filter(unbounded).count();
                let free = twice.iter().filter(|v| &***v != "N").count();
                if twice.contains("N") != (places >= 2) || names != free {
                    bad.push(format!(
                        "`{text}` prints `{shown}`: standing twice {twice:?}"
                    ));
                }
                n += 1;
            }
        }
    }
    // The generator reaches both outcomes for `N`, or the test would show nothing.
    assert!(
        named_once > 0 && named_twice > 0,
        "{named_once} {named_twice}"
    );
    assert!(
        bad.is_empty(),
        "{} of {n} signatures differ; the first:\n{}",
        bad.len(),
        bad[..bad.len().min(30)].join("\n")
    );
}
