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

/// The entry `e` of `xs` at a key `i` the caller gives is passed at `f`, and stands in one
/// place of the type of `k`: inside the type of `h`, the function `k` returns. It prints as
/// the type it is passed at, not `_`. At the fixed key 0, `xs` is used only by lookup and
/// prints as the map `0 -> T` (row PRINT-hidden-var), which puts `e` in a second place: it
/// then prints `T`, which keeps the link between the entry and the result.
#[test]
fn a_variable_in_one_place_inside_a_held_function_prints_as_its_bound() {
    let src = format!(
        "{APPLY}k(xs, i) = {{\n  e = xs[i];\n  h(positional y) = (apply(f: e), e);\n  h\n}};\na = k(xs: [1], i: 0);\n"
    );
    let out = report(&src);
    assert!(
        out.contains(
            "the type the checker found for `k` is `(xs: _, i: _) -> _ -> (int, (x: int | f64) ->? int)`"
        ),
        "{src}\n{out}"
    );
    let src = format!(
        "{APPLY}k(xs) = {{\n  e = xs[0];\n  h(positional y) = (apply(f: e), e);\n  h\n}};\na = k(xs: [1]);\n"
    );
    let out = report(&src);
    assert!(
        out.contains("the type the checker found for `k` is `(xs: 0 -> T) -> _ -> (int, T)`"),
        "{src}\n{out}"
    );
}

/// `v` stands in the parameter and in the union `v | E` of the result, where `E`, the type of
/// the entry `xs[0]`, stands in that union only and so prints `_`. That union prints `_` alone,
/// since `_` holds every value, so `v` stands in one place of the text and prints as the type
/// it is passed at. Here the key `i` is the caller's; at the fixed key 0, `xs` prints as the
/// map `0 -> U` (row PRINT-hidden-var), so `E` prints `U`, the union `T | U` is no longer `_`,
/// and `v` stands in two places and prints `T`.
#[test]
fn a_variable_whose_other_place_is_a_union_printed_blank_prints_as_its_bound() {
    let src = format!(
        "{APPLY}k(v, xs, i, c: bool) = (apply(f: v), if c {{ v }} else {{ xs[i] }});\na = k(v: 3, xs: [1], i: 0, c: true);\n"
    );
    let out = report(&src);
    assert!(
        out.contains(
            "the type the checker found for `k` is `(v: (x: int | f64) ->? int, xs: _, i: _, c: bool) -> (int, _)`"
        ),
        "{src}\n{out}"
    );
    let src = format!(
        "{APPLY}k(v, xs, c: bool) = (apply(f: v), if c {{ v }} else {{ xs[0] }});\na = k(v: 3, xs: [1], c: true);\n"
    );
    let out = report(&src);
    assert!(
        out.contains(
            "the type the checker found for `k` is `(v: T, xs: 0 -> U, c: bool) -> (int, T | U)`"
        ),
        "{src}\n{out}"
    );
    // The note of what `k` takes says `v`'s bound by the name of its variable (plan row
    // MSG-takes-note-names-var), a name the message gives as it gives the other notes' names
    // (MSG-takes-note-name-shared): the same variable is `T` in both notes, not `T` in this
    // one and, the name a word the others skip, `U` in the other.
    assert!(
        out.contains(
            "`k` takes (v: T, xs: 0 -> U, c: bool) -> (int, T | U), where T is not int | f32 | f64 | rat | bool | String"
        ),
        "{src}\n{out}"
    );
}

/// What the failed test `r is #a` leaves of `r` prints with the variable of `r` (DESIGN.md
/// sec:diagnostics: "What an `else` or a failed test leaves of a value prints with the
/// variable of that value and the type former that removes the rest"), so the two stand in two
/// places and print `T`, though what is left is passed at `f`; the leftover in the result
/// prints `T \ #a` (else1x1).
#[test]
fn what_a_failed_test_leaves_prints_with_the_variable_of_the_value() {
    let src = format!(
        "{APPLY}k(r) = if r is #a {{ (0, 0) }} else {{ (apply(f: r), r) }};\na = k(r: 3);\n"
    );
    let out = report(&src);
    assert!(
        out.contains("the type the checker found for `k` is `(r: T) -> (0, 0) | (int, T \\ #a)`"),
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

/// Row PERF-standing-twice-shared-empty: [`Sig::standing_twice`] walks a tuple with variables
/// that the print writes once (`Shared::local`, crates/zedc-types/src/ty.rs) once, and counts each place of
/// a variable bounded by carriers inside it once for each place of the tuple. Here `N` stands
/// only in the tuple `(N, int)`, held once inside each of the parameters `(S, int)`, so twice
/// below a part: it stands twice, as the text, which writes that short tuple in full at both
/// places, shows. With one place of the tuple it stands once. A count of the places the walk
/// writes, the tuple's text once, would give one for both.
#[test]
fn a_bounded_variable_in_a_tuple_written_once_stands_at_each_place_of_the_tuple() {
    use std::sync::Arc;
    use zedc::check::ty::Binds;
    let inner = read_sig("((x: (N, int)) -> int for N in int | f64)");
    let row = inner.arrows[0].params[0].clone();
    for (arrows, want) in [
        ("(a: (S, int), b: (S, int)) -> int", true),
        ("(a: (S, int), b: int) -> int", false),
    ] {
        let s = read_sig(arrows);
        let binds: Binds = [(Arc::<str>::from("S"), row.clone())].into();
        let mut s = s.replace(&binds);
        s.own.retain(|v| &**v != "S");
        s.bounds = inner.bounds.clone();
        let shown = s.to_string();
        assert_eq!(places_of(&shown, "N"), 1 + usize::from(want), "{shown}");
        assert_eq!(s.standing_twice().contains("N"), want, "{shown}");
    }
}

/// `arrows` with its variable `S` replaced by `row`, its own variables but `S` kept, and the
/// bounds of `bounds`.
fn with_row(
    arrows: &str,
    row: &zedc::check::ty::Ty,
    bounds: &zedc::check::ty::Sig,
) -> zedc::check::ty::Sig {
    use std::sync::Arc;
    use zedc::check::ty::Binds;
    let binds: Binds = [(Arc::<str>::from("S"), row.clone())].into();
    let mut s = read_sig(arrows).replace(&binds);
    s.own.retain(|v| &**v != "S");
    s.own.extend(bounds.bounds.keys().cloned());
    s.bounds = bounds.bounds.clone();
    s
}

/// XR-heldname-print-batch round 1, Codex B4-N: the places of a bounded variable inside a
/// tuple written once fall with the places of the tuple a union printed `_` erases. The tuple
/// `(N, int)` is one node at both places; a union of it and a variable standing once (`P`, `Q`)
/// prints `_` alone. With no place erased `N` stands twice; with one erased, once; with both
/// erased, nowhere. The text shows the same.
#[test]
fn a_bounded_variable_falls_with_the_erased_places_of_its_tuple() {
    let inner = read_sig("((x: (N, int)) -> int for N in int | f64)");
    let row = inner.arrows[0].params[0].clone();
    for (arrows, places) in [
        ("(a: int) -> (S, S)", 2),
        ("(a: int) -> (S, P | S)", 1),
        ("(a: int) -> (P | S, Q | S)", 0),
    ] {
        let s = with_row(arrows, &row, &inner);
        let shown = s.to_string();
        assert_eq!(places_of(&shown, "N"), places, "{arrows}: {shown}");
        assert_eq!(
            s.standing_twice().contains("N"),
            places >= 2,
            "{arrows}: {shown}"
        );
    }
}

/// XR-heldname-print-batch round 1, Codex B2: the places of a tuple written once as a
/// definition cross from two or more to one and to none as unions printed `_` erase them,
/// each count capped at two (`Weights`). The tuple R_6 (R_0 = `(T, T)`, R_{i+1} = `(R_i,
/// R_i)`, one node at both places) stands three times, two of them in one pair: 2+1, then 2,
/// 1 and 0 places left. At two or more it is a definition, the sixth and last, named at each
/// place left; at one it is written once there, as `(Part5, Part5)`, its rows inside still
/// named (five definitions, the last named twice); at none no definition is written. Each
/// text reads back and prints again to itself.
#[test]
fn shared_tuple_places_cross_two_then_one_without_losing_the_definition() {
    use zedc::check::ty::Ty;
    let bounded = read_sig("(a: T) -> T for T in int | f64");
    let t = bounded.arrows[0].result.clone();
    let row = (0..6).fold(Ty::tuple(vec![t.clone(), t]), |r, _| {
        Ty::tuple(vec![r.clone(), r])
    });
    let mut report = Vec::new();
    let mut bad = 0;
    for (arrows, left) in [
        ("(a: T) -> ((S, S), S)", 3),
        ("(a: T) -> ((S, S), P | S)", 2),
        ("(a: T) -> ((S, Q | S), P | S)", 1),
        ("(a: T) -> ((R | S, Q | S), P | S)", 0),
    ] {
        let s = with_row(arrows, &row, &bounded);
        let text = s.to_string();
        let defs = text.matches("type Part").count();
        let line = text.lines().last().unwrap_or("");
        let last = format!("Part{defs}");
        let named = line.matches(last.as_str()).count();
        let back = zedc::check::read::parse_type(&text).map(|b| b.to_string());
        let ok = match left {
            0 => defs == 0,
            1 => defs == 5 && named == 2,
            _ => defs == 6 && named == left,
        } && back.as_deref() == Ok(text.as_str());
        bad += usize::from(!ok);
        report.push(format!(
            "{arrows}, {left} left: {}\n{text}\n  {defs} definitions, {last} named {named} times in the signature; read back: {back:?}",
            if ok { "ok" } else { "WRONG" }
        ));
    }
    assert_eq!(bad, 0, "\n{}", report.join("\n"));
}

/// Row TEST-takes-note-name-in-definition: the result of `k` holds tuples written once, as
/// definitions (row PRINT-shared-part-exponential), whose variables are unbounded, beside a
/// variable bounded by `apply`'s parameter. The note of what `k` takes and the type the
/// checker found share the message's one block of definitions, and name each variable as it
/// does, inside the definitions and out (MSG-takes-note-name-shared): the bounded one, last
/// (`T6`) or first (`T`) among the parameters, and those of the definitions, which start at
/// `U` when the bounded one is `T`. The bounded one, bounded by a need and not by carriers,
/// stands only in the outermost tuple, so it stays outside the definitions.
#[test]
fn the_takes_note_names_the_variables_of_a_definition_as_the_type_does() {
    let p = "p(positional s, positional v) = (s, (s, v));\n";
    let bound = "where T6 is not int | f32 | f64 | rat | bool | String";
    let src = format!(
        "{APPLY}{p}k(positional a0, positional a1, positional a2, positional a3, positional a4, positional a5) = (apply(f: a5), p(p(p(p(p(a0, a1), a2), a3), a4), a5));\na = k(1, 2, 4, 5, 6, 3);\n"
    );
    let out = report(&src);
    for want in [
        "  Part1, Part2 and Part3 stand for parts written more than once:\n    type Part1 = ((T, (T, U)), ((T, (T, U)), V));\n    type Part2 = (Part1, (Part1, W));\n    type Part3 = (Part2, (Part2, T5));\n",
        format!("`k` takes (T, U, V, W, T5, T6) -> (int, (Part3, (Part3, T6))), {bound}\n")
            .as_str(),
        "the type the checker found for `k` is `(T, U, V, W, T5, T6) -> (int, (Part3, (Part3, T6)))`",
    ] {
        assert!(out.contains(want), "{src}\nwants {want}\n{out}");
    }
    let bound = "where T is not int | f32 | f64 | rat | bool | String";
    let src = format!(
        "{APPLY}{p}k(positional b, positional a0, positional a1, positional a2, positional a3) = (apply(f: b), p(p(p(p(a0, a1), a2), a3), b));\na = k(3, 1, 2, 4, 5);\n"
    );
    let out = report(&src);
    for want in [
        "  Part1 and Part2 stand for parts written more than once:\n    type Part1 = ((U, (U, V)), ((U, (U, V)), W));\n    type Part2 = (Part1, (Part1, T5));\n",
        format!("`k` takes (T, U, V, W, T5) -> (int, (Part2, (Part2, T))), {bound}\n").as_str(),
        "the type the checker found for `k` is `(T, U, V, W, T5) -> (int, (Part2, (Part2, T)))`",
    ] {
        assert!(out.contains(want), "{src}\nwants {want}\n{out}");
    }
}
