//! The solver in the checker, end to end through `zedc run`: a linear question the solver
//! decides rejects nothing, and one it refuses is a rejection with its cause, its span and
//! the constraints.

use zed_tests::step_helpers::l01_19_whole_file_ports::run;
use zed_tests::step_helpers::l01_25_preimage_catalog::int_defs;

/// A program whose `main` calls `ok`, defined by `def`, at `args`, and prints whether it held;
/// `a` in `args` is the integer on the first line of the input (key 0 of the lines), or 0. Each
/// parameter `def` writes without a type is declared `int` ([`int_defs`]): the checker asks a
/// linear question only of a function whose parameters are all `int`, and a bare literal takes
/// the carrier of its use (L1.26a), so it no longer makes a parameter `int`.
fn program(def: &str, args: &str) -> String {
    let def = int_defs(def);
    format!(
        "{def}\nmain(m: MainArgs) {{\n  a = int(m.stdin[0] else \"0\") else 0;\n  \
         r = if ok({args}) {{ \"in\" }} else {{ \"out\" }};\n  m.stdout <- \"${{r}}\";\n}}\n"
    )
}

/// The standard error of a rejected run, with the program's path removed from its first line,
/// and without the source lines the steps underline. The program is written in test directory
/// `name`, so two tests, which may run at once, give two names.
fn rejection(name: &str, src: &str) -> String {
    let o = run(name, src, "3\n", &[]);
    assert_eq!((o.status, o.stdout.as_str()), (1, ""), "{}", o.stderr);
    let (_, rest) = o.stderr.split_once("prog.zed:").expect("a placed message");
    let mut lines = rest.lines();
    let first = lines.next().expect("a message");
    std::iter::once(first)
        .chain(lines.filter(|l| l.trim_start().starts_with('[')))
        .collect::<Vec<_>>()
        .join("\n")
}

/// A printed refusal without its menu: the cause and the constraints, which a question asked
/// through a call shares with the question written out, while the menu rewrites each function
/// as it is written.
fn stated(printed: &str) -> String {
    (printed.lines())
        .filter(|l| !l.contains(": repair: "))
        .collect::<Vec<_>>()
        .join("\n")
}

/// The start of the refusal of `ok(params) = rows;`, up to its cause: the condition on one line,
/// as the message prints it, and the parameters each quoted.
fn head(rows: &str, params: &str) -> String {
    let condition = rows.split_whitespace().collect::<Vec<_>>().join(" ");
    let names = (params.split(", "))
        .map(|p| format!("`{}`", p.split(':').next().unwrap_or(p)))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "1:1: zedc could not decide whether the condition of `ok`, written `{condition}`, can be \
         true for whole-number values of {names}, which it works out for every test function: "
    )
}

/// `text` without the condition each refusal in it quotes as written, so that a question
/// written through a call and the same question written out compare equal.
fn unwritten(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(from) = rest.find(", written `") {
        let Some(to) = rest[from..].find("`, can be ") else {
            break;
        };
        out.push_str(&rest[..from]);
        rest = &rest[from + to + 1..];
    }
    out.push_str(rest);
    out
}

/// The condition of the definition `def` as written: the body of an equation without its `;`,
/// or the whole block.
fn condition_of(def: &str) -> &str {
    match def.split_once(") = ") {
        Some((_, body)) => body.strip_suffix(';').expect("one equation"),
        None => &def[def.find('{').expect("a block")..],
    }
}

/// [`head`] for the `ok` defined on the first line of `src`, as `ok(x, y) = rows;`.
fn head_in(src: &str) -> String {
    let def = src.lines().next().expect("a definition");
    let (params, rest) = (def.strip_prefix("ok("))
        .and_then(|d| d.split_once(") = "))
        .expect("`ok` first");
    head(rest.strip_suffix(';').expect("one line"), params)
}

/// The repairs of a printed refusal's menu, each after `repair: `.
fn repairs(printed: &str) -> Vec<&str> {
    (printed.lines())
        .filter_map(|l| l.split_once(": repair: ").map(|(_, r)| r))
        .collect()
}

/// The definitions a repair writes out: its code spans that define `ok` or a function named
/// `ok` and a number whole, up to the `;` or `}` that ends them.
fn definitions(repair: &str) -> Vec<&str> {
    (repair.split('`').skip(1).step_by(2))
        .filter(|c| {
            let rest = c.strip_prefix("ok").unwrap_or("");
            let rest = rest.trim_start_matches(|d: char| d.is_ascii_digit());
            rest.starts_with("(x") && (c.ends_with(';') || c.ends_with('}'))
        })
        .collect()
}

/// The program [`program`] gives at `args` once `repair` is followed as it says: a
/// definition of `ok` in place of `ok`'s, or two definitions, `ok1` and `ok2` or the names
/// the repair gives, whose results are joined where `ok` was called.
fn repaired(repair: &str, args: &str) -> String {
    repaired_beside("", repair, args)
}

/// [`repaired`] in a program that defines `defs` before the repair's definitions.
fn repaired_beside(defs: &str, repair: &str, args: &str) -> String {
    let name = |d: &str| d.split_once('(').expect("a definition").0.to_string();
    match definitions(repair)[..] {
        [d] => program(&format!("{defs}{d}"), args),
        [d1, d2] => program_testing(
            &format!("{defs}{d1}\n{d2}"),
            &format!("{}({args}) && {}({args})", name(d1), name(d2)),
        ),
        _ => panic!("a repair with no definitions to follow: {repair}"),
    }
}

/// A refused `ok` over `x, y, z, w`, its conditions in two parts.
struct Refused {
    name: &'static str,
    rows: [&'static str; 2],
}

const REFUSED: [Refused; 3] = [
    // Growth: no elimination keeps the four rows within their count.
    Refused {
        name: "growth",
        rows: [
            "4 * x - 12 * w - 10 * y - 12 * z + 11 >= 0 && 4 * w + 10 * x - 10 * y - 11 * z - 28 \
             >= 0",
            "11 * w + 4 * x - y + 12 * z - 28 >= 0 && -8 * w - 5 * x + 12 * y - z + 31 >= 0",
        ],
    },
    // Shadows: a point could lie only in a splinter that would be split again with as many
    // variables left.
    Refused {
        name: "shadows",
        rows: [
            "9 * x - 4 * y - 8 * w - 3 >= 0 && 5 * x + 11 * y + 9 * w - 9 >= 0 && -7 * x - 12 * \
             y - 2 * z + 8 * w - 1 >= 0",
            "-9 * x + 8 * y + 7 * z >= 0 && -10 * x + 4 * y - 6 * z - 4 * w + 22 >= 0",
        ],
    },
    // Tie: the cycle `3 * next - this >= 10`, whose four names occur alike and share rows.
    Refused {
        name: "tie",
        rows: [
            "3 * y - x - 10 >= 0 && 3 * z - y - 10 >= 0",
            "3 * w - z - 10 >= 0 && 3 * x - w - 10 >= 0",
        ],
    },
];

/// The menu a refused `ok(x, y, z, w)` with conditions `body` prints at L1, numbered after its
/// note of constraints and placed, as that note is, at the body, which begins at column 38 of
/// line 1, after `ok(x: int, y: int, z: int, w: int) = ` ([`program`]): a value stated for
/// `v`, the order `a <= b` when one is given, and the conditions split into `split` (DESIGN.md
/// sec:diagnostics, row "Linear question outside the polynomial fragment").
fn menu(v: &str, order: Option<(&str, &str)>, body: &str, split: [&str; 2]) -> String {
    const P: &str = "x: int, y: int, z: int, w: int";
    const HEAD: &str = "ok(x: int, y: int, z: int, w: int) = ";
    let mut lines = vec![format!(
        "repair: if `{v}` is meant to take only one value in `ok`, state that value, and the \
         checker removes `{v}` from the question: `{HEAD}{v} == 0 && {body};`, with the value in \
         place of `0`"
    )];
    if let Some((a, b)) = order {
        lines.push(format!(
            "repair: if `{a} <= {b}` is meant to hold in `ok`, state it, and the checker can tell \
             `{a}` and `{b}` apart: `{HEAD}{a} <= {b} && {body};`"
        ));
    }
    lines.push(format!(
        "repair: split the conditions between two functions, `ok1` and `ok2`, and where `ok` \
         is called, call `ok1(…) && ok2(…)` with the same arguments; each asks a smaller \
         question, and a function whose body joins them asks the joined question again: \
         `ok1({P}) = {};` and `ok2({P}) = {};`",
        split[0], split[1]
    ));
    (lines.iter().enumerate())
        .map(|(i, l)| format!("[{}] 1:38: {l}", i + 2))
        .collect::<Vec<_>>()
        .join("\n  ")
}

/// A program like [`program`]'s whose `main` tests `test` in place of a call of `ok`.
fn program_testing(defs: &str, test: &str) -> String {
    let defs = int_defs(defs);
    format!(
        "{defs}\nmain(m: MainArgs) {{\n  a = int(m.stdin[0] else \"0\") else 0;\n  \
         r = if {test} {{ \"in\" }} else {{ \"out\" }};\n  m.stdout <- \"${{r}}\";\n}}\n"
    )
}

/// A refused question of each kind, at L1: the cause's opening words, the menu's repairs in
/// order (stating a value; for two variables alike, stating their order; splitting the
/// conditions), and, followed as it is printed, each repair makes the program check and run.
#[test]
fn following_each_repair_of_the_menu_makes_the_program_check() {
    const GROWTH: &str = "to find whole numbers that meet these conditions, the checker \
                          removes one variable at a time, putting in place of the conditions \
                          on it conditions on the variables left. Here four variables or more";
    const SHADOWS: &str = "to find whole numbers that meet these conditions, the checker \
                           removes one variable at a time, putting in place of the conditions \
                           on it conditions on the variables left. Where the values";
    const TIE: &str = "to find whole numbers that meet these conditions, the checker removes \
                       one variable at a time, putting in place of the conditions on it \
                       conditions on the variables left. Its next step must choose among";
    const ALTERNATIVES: &str = "the conditions hold alternatives, where one of several cases \
                                is enough (from `||`, from `!=`, which holds when either side \
                                is the larger, or from a negated `&&`), and the checker looks \
                                for a choice of one case from each alternative that can hold \
                                with the rest";
    // (name, parameters, the definition of `ok`, the cause's opening words, whether `ok` holds
    // at input 0 and at input 5, the variables of the order repair if it is offered).
    let both = |r: &Refused| format!("ok(x, y, z, w) = {} && {};", r.rows[0], r.rows[1]);
    let cases = [
        ("growth", "x, y, z, w", both(&REFUSED[0]), GROWTH.to_string(), ["out\n", "out\n"], None),
        ("shadows", "x, y, z, w", both(&REFUSED[1]), SHADOWS.to_string(), ["out\n", "out\n"], None),
        // At x = y = z = w = 5 the cycle holds (3 * 5 - 5 = 10).
        ("tie", "x, y, z, w", both(&REFUSED[2]), TIE.to_string(), ["out\n", "in\n"], Some(("w", "x"))),
        // Four names in 0..=2 that differ pairwise: no point, which the search through the
        // disjunctions of `!=` does not settle.
        (
            "disjuncts",
            "x, y, z, w",
            "ok(x, y, z, w) = 0 <= x && x <= 2 && 0 <= y && y <= 2 && 0 <= z && z <= 2 && 0 <= w \
             && w <= 2 && x != y && x != z && y != z && x != w && y != w && z != w;"
                .to_string(),
            format!("{ALTERNATIVES}; no choice it tried has values"),
            ["out\n", "out\n"],
            None,
        ),
        // Two shifts in 0..=9, each early or late, with a total from 1 to 10: `x` and `y`
        // occur alike, so only their names could order the search
        // (`l01_38_presburger::names`, the shifts with `1 <= x + y <= 10`). Without
        // `1 <= x + y`, the shifts at their lower bounds, `x == 0 && y == 0`, are a point,
        // found before any search.
        (
            "unordered",
            "x, y",
            "ok(x, y) = 0 <= x && x <= 9 && 0 <= y && y <= 9 && 1 <= x + y && x + y <= 10 && (x \
             <= 2 || x >= 7) && (y <= 2 || y >= 7);"
                .to_string(),
            format!("{ALTERNATIVES}. After every case that cannot hold is removed"),
            ["out\n", "out\n"],
            Some(("x", "y")),
        ),
        // The tie in a block that names a part of a condition and returns the conditions: the
        // repairs rewrite the value it returns and keep the rest of the block.
        (
            "tie-block",
            "x, y, z, w",
            "ok(x, y, z, w) {\n  t = 3 * y - x - 10;\n  return t >= 0 && 3 * z - y - 10 >= 0 && 3 * w \
             - z - 10 >= 0 && 3 * x - w - 10 >= 0;\n}"
                .to_string(),
            TIE.to_string(),
            ["out\n", "in\n"],
            Some(("w", "x")),
        ),
    ];
    for (name, params, def, cause, outs, order) in cases {
        let args: Vec<String> = params.split(", ").map(|p| format!("{p}: a")).collect();
        let args = args.join(", ");
        let printed = rejection(name, &program(&def, &args));
        assert!(
            printed.starts_with(&format!("{}{cause}", head(condition_of(&def), params))),
            "{printed}"
        );
        let menu = repairs(&printed);
        let first = menu[0];
        assert!(
            first.starts_with("if `")
                && first.contains("` is meant to take only one value in `ok`"),
            "{name}: {first}"
        );
        let mut want = vec![first];
        if let Some((a, b)) = order {
            want.push(menu[1]);
            assert!(
                menu[1].starts_with(&format!(
                    "if `{a} <= {b}` is meant to hold in `ok`, state it"
                )),
                "{name}: {}",
                menu[1]
            );
        }
        let split = menu[want.len()];
        assert!(
            split.starts_with("split the conditions between two functions, `ok1` and `ok2`"),
            "{name}: {split}"
        );
        want.push(split);
        assert_eq!(menu, want, "{name}");
        // Each repair, followed as printed, makes the question decided, and `ok` then holds
        // where it held before, but for the stated value, `0`, which input 5 does not meet.
        for (k, repair) in menu.iter().enumerate() {
            let src = repaired(repair, &args);
            for (input, out) in ["0\n", "5\n"].into_iter().zip(outs) {
                let o = run(&format!("{name}-{k}"), &src, input, &[]);
                let out = if k == 0 && input == "5\n" {
                    "out\n"
                } else {
                    out
                };
                assert_eq!(
                    (o.status, o.stdout.as_str(), o.stderr.as_str()),
                    (0, out, ""),
                    "{name} repair {k} at {input}{src}"
                );
            }
        }
    }
}

/// A program that already defines `ok1`, or `ok1` and `ok2`, with the parameters of `ok`, gets
/// a split repair whose two functions take the first names after `ok` and a number that the
/// program leaves free; followed as printed, beside the program's own definitions, it makes
/// the program check and run. Named `ok1` and `ok2` there, the repair would define a function
/// a second time with the same parameter types, which is an error (DESIGN.md, the binding
/// rule of the syntax table).
#[test]
fn the_split_repair_names_functions_the_program_does_not_define() {
    let [first, second] = REFUSED[2].rows;
    let def = format!("ok(x, y, z, w) = {first} && {second};");
    let args = "x: a, y: a, z: a, w: a";
    let cases = [
        ("taken-1", "ok1(x, y, z, w) = x <= y;\n", ["ok2", "ok3"]),
        (
            "taken-2",
            "ok1(x, y, z, w) = x <= y;\nok2(x, y, z, w) = y <= z;\n",
            ["ok3", "ok4"],
        ),
    ];
    for (name, defs, [a, b]) in cases {
        let printed = rejection(name, &program(&format!("{defs}{def}"), args));
        let menu = repairs(&printed);
        let split = *menu.last().expect("a menu");
        // Followed as printed, beside the program's definitions, the split checks and runs:
        // the tie's cycle holds at input 5 and not at 0.
        let src = repaired_beside(defs, split, args);
        for (input, out) in [("0\n", "out\n"), ("5\n", "in\n")] {
            let o = run(&format!("{name}-split"), &src, input, &[]);
            assert_eq!(
                (o.status, o.stdout.as_str(), o.stderr.as_str()),
                (0, out, ""),
                "{name} at {input}{src}"
            );
        }
        assert!(
            split.starts_with(&format!(
                "split the conditions between two functions, `{a}` and `{b}`, and where `ok` \
                 is called, call `{a}(…) && {b}(…)` with the same arguments"
            )),
            "{name}: {split}"
        );
        let heads: Vec<&str> = (definitions(split).iter())
            .map(|d| d.split_once(" = ").expect("a definition").0)
            .collect();
        let want = [a, b].map(|f| format!("{f}(x: int, y: int, z: int, w: int)"));
        assert_eq!(heads, want, "{name}: {split}");
    }
}

/// The split repair of a refused question in a unit `pricing` that a unit `app` imports, where
/// `app` already defines `ok1` and `ok2` with the parameters of `ok`: the repair still names its
/// functions `ok1` and `ok2`, as it does for `pricing` checked alone, and followed as printed it
/// clashes with nothing in `app` (DESIGN.md sec:diagnostics, "Names the split repair adds").
/// An importer reaches a unit's names only through the names its imports and qualified uses
/// write, since there is no wildcard import (sec:units), so `app`'s own `ok1` and `pricing.ok1`
/// stay two names. Were the repair to avoid `app`'s names as well, it would print `ok3` and
/// `ok4` here, and `ok1` and `ok2` when `pricing` is checked alone: two answers for one text.
#[test]
fn the_split_repair_in_an_imported_unit_ignores_the_names_its_importers_define() {
    use zedc::query::Db;
    use zedc::resolve::Ref;
    use zedc::unit::{Memory, Package, load};

    let [first, second] = REFUSED[2].rows;
    let pricing = int_defs(&format!("ok(x, y, z, w) = {first} && {second};"));
    let own = "ok1(x: int, y: int, z: int, w: int) = x <= y;\n\
               ok2(x: int, y: int, z: int, w: int) = y <= z;\n";
    let all = "x: a, y: a, z: a, w: a";
    let app = |imports: &str, test: &str| {
        format!(
            "{imports}{own}main(m: MainArgs) {{\n  a = int(m.stdin[0] else \"0\") else 0;\n  \
             r = if {test} {{ \"in\" }} else {{ \"out\" }};\n  m.stdout <- \"${{r}}\";\n}}\n"
        )
    };
    let package = |db: &mut Db, pricing: &str, app: &str| -> Package {
        let files = [("pricing.zed", pricing), ("app.zed", app)]
            .map(|(f, t)| (f.to_string(), std::sync::Arc::from(t)));
        load(db, &Memory(files.into_iter().collect()), &["app"])
    };
    // The problems of a package, but for the forms a later step links.
    let problems = |p: &Package| -> Vec<String> {
        (p.report(std::path::Path::new("")).into_iter())
            .filter(|m| !zed_tests::is_not_yet(m))
            .collect()
    };
    let refusal = |db: &mut Db| match &*db.front(&pricing) {
        Err(ds) => ds.clone(),
        Ok(_) => panic!("`ok` is refused in\n{pricing}"),
    };

    // `pricing` checked alone, with no importer.
    let alone = refusal(&mut Db::new());
    // `pricing` in the build of `app`, which imports it in each form and defines `ok1` and `ok2`.
    let mut db = Db::new();
    let before = app(
        "import pricing;\nimport pricing as p;\nimport pricing.{ok};\n",
        &format!("ok({all}) && ok1({all}) && ok2({all})"),
    );
    let built = package(&mut db, &pricing, &before);
    assert_eq!(problems(&built), Vec::<String>::new(), "{before}");
    let imported = refusal(&mut db);
    assert_eq!(imported, alone);
    let [d] = &alone[..] else {
        panic!("one refusal: {alone:?}")
    };
    let printed = d.to_string();
    let split = *repairs(&printed).last().expect("a menu");
    assert!(
        split.starts_with(
            "split the conditions between two functions, `ok1` and `ok2`, and where `ok` is \
             called, call `ok1(…) && ok2(…)` with the same arguments"
        ),
        "{split}"
    );

    // Followed as printed: `pricing` holds the two functions, `app` calls them through its
    // qualifiers where it called `ok`, and its own `ok1` and `ok2` are unchanged.
    let repaired = definitions(split).join("\n");
    let after = app(
        "import pricing;\nimport pricing as p;\n",
        &format!("pricing.ok1({all}) && p.ok2({all}) && ok1({all}) && ok2({all})"),
    );
    let mut db = Db::new();
    assert!(db.front(&repaired).is_ok(), "{repaired}");
    let built = package(&mut db, &repaired, &after);
    assert_eq!(problems(&built), Vec::<String>::new(), "{after}");
    let r = (built.unit("app").and_then(|u| u.resolved.as_ref())).expect("`app` resolved");
    // What the use of `name` at the `n`-th place `name(` is written in `app` resolves to.
    let use_at = |name: &str, n: usize| {
        let (at, _) = (after.match_indices(&format!("{name}(")))
            .filter(|(i, _)| !after[..*i].ends_with(|c: char| c == '.' || c.is_alphanumeric()))
            .nth(n)
            .unwrap_or_else(|| panic!("no use {n} of `{name}` in\n{after}"));
        let (_, used) = (r.res.uses.iter())
            .find(|(s, _)| (s.start, s.end) == (at, at + name.len()))
            .unwrap_or_else(|| panic!("`{name}` at {at} is no recorded use"));
        used.clone()
    };
    for (qualified, name) in [("pricing.ok1", "ok1"), ("p.ok2", "ok2")] {
        let used = use_at(qualified, 0);
        assert!(
            matches!(&used, Ref::Unit { unit, name: n } if &**unit == "pricing" && n == name),
            "{qualified}: {used:?}"
        );
    }
    // The bare `ok1` and `ok2` of `main` (the second place each is written, after its
    // definition) are `app`'s own definitions, one arrow each, imported from nowhere.
    for name in ["ok1", "ok2"] {
        let Ref::Bound(ids) = use_at(name, 1) else {
            panic!("`{name}` is not bound in `app`")
        };
        let ids: Vec<usize> = ids.into_iter().collect();
        let [i] = ids[..] else {
            panic!("`{name}` is an overload set of {ids:?}")
        };
        let b = &r.res.binders[i];
        assert!(after[b.span.start..].starts_with(name), "{name}: {b:?}");
        assert_eq!(r.res.imports.get(&i), None, "{name}");
    }
}

#[test]
fn a_function_that_joins_the_split_questions_asks_the_joined_question_again() {
    // The second half of the split repair's line: joining `first` and `second` in a function
    // other than `main` inlines both, and the joined question is refused as before.
    let [first, second] = REFUSED[0].rows;
    let src = program(
        &format!(
            "first(x, y, z, w) = {first};\nsecond(x, y, z, w) = {second};\nok(x, y, z, w) = \
             first(x:, y:, z:, w:) && second(x:, y:, z:, w:);"
        ),
        "x: a, y: a, z: a, w: a",
    );
    let o = run("joined", &src, "3\n", &[]);
    assert_eq!(o.status, 1, "{}", o.stderr);
    assert!(
        o.stderr
            .contains("zedc could not decide whether the condition of `ok`"),
        "{}",
        o.stderr
    );
}

#[test]
fn pughs_example_is_decided_and_its_arm_is_unreachable() {
    // 27 <= 11x + 13y <= 45, -10 <= 7x - 9y <= 4 has rational points and no integer point:
    // the test never holds, which is an unreachable arm, not a rejection.
    let src = program(
        "ok(x, y) = 27 <= 11 * x + 13 * y && 11 * x + 13 * y <= 45 && -10 <= 7 * x - 9 * y && \
         7 * x - 9 * y <= 4;",
        "x: a, y: a + 1",
    );
    for input in ["0\n", "1\n", "3\n", "-2\n"] {
        let o = run("pugh", &src, input, &[]);
        assert_eq!(
            (o.status, o.stdout.as_str(), o.stderr.as_str()),
            (0, "out\n", ""),
            "{input}"
        );
    }
}

#[test]
fn shifts_that_hold_at_their_lower_bounds_are_decided() {
    // Two shifts in 0..=9, each early or late, with a total of at most 10: `x` and `y` occur
    // alike, and the search through the cases would be refused for their order, as it is with
    // `1 <= x + y` as well (`following_each_repair_of_the_menu_makes_the_program_check`); but
    // each shift at its lower bound, 0, meets every condition, so the test can hold and the
    // program checks and runs.
    let src = program(
        "ok(x, y) = 0 <= x && x <= 9 && 0 <= y && y <= 9 && x + y <= 10 && (x <= 2 || x >= 7) \
         && (y <= 2 || y >= 7);",
        "x: a, y: a",
    );
    for (input, out) in [
        ("0\n", "in\n"),
        ("1\n", "in\n"),
        ("5\n", "out\n"),
        ("7\n", "out\n"),
    ] {
        let o = run("shifts", &src, input, &[]);
        assert_eq!(
            (o.status, o.stdout.as_str(), o.stderr.as_str()),
            (0, out, ""),
            "{input}"
        );
    }
}

#[test]
fn a_satisfiable_question_with_no_elimination_that_keeps_the_rows_is_refused() {
    // The rows hold at (x, y, z, w) = (4, 0, 1, 0), where they are 15, 1, 0 and 10, so `ok` can
    // hold; the refusal claims only that this is not decided, since every elimination would add
    // terms and the box of the bounds and its five points settle nothing.
    let src = program(
        "ok(x, y, z, w) = 4 * x - 12 * w - 10 * y - 12 * z + 11 >= 0 && 4 * w + 10 * x - 10 * y \
         - 11 * z - 28 >= 0 && 11 * w + 4 * x - y + 12 * z - 28 >= 0 && -8 * w - 5 * x + 12 * y \
         - z + 31 >= 0;",
        "x: a, y: a, z: a, w: a",
    );
    assert_eq!(
        rejection("growth-alone", &src),
        format!(
            "{}to find whole numbers that meet these \
             conditions, the checker removes one variable at a time, putting in place of the \
             conditions on it conditions on the variables left. Here four variables or more \
             are left, and removing any one of them would leave more conditions than there are \
             now, so the work could grow without end. The checker stopped there, with no \
             values found and none ruled out.\n  \
             [1] 1:38: the constraints: 12 * w + 10 * y + 12 * z <= 4 * x + 11 && 4 * w + 10 * \
             x >= 10 * y + 11 * z + 28 && 11 * w + 4 * x + 12 * z >= y + 28 && 8 * w + 5 * x + \
             z <= 12 * y + 31\n  {}",
            head_in(&src),
            menu("x", None, &REFUSED[0].rows.join(" && "), REFUSED[0].rows)
        )
    );
}

#[test]
fn a_bound_past_the_64_bit_range_keeps_the_question() {
    // PNCX-modular, R4 (I4.1): the question above with `x < 2^63` (and `x < 2^64`) added is
    // refused as it is with `x < 2^63 - 1`, its bound printed at its size; a literal past the
    // 64-bit range read as no linear form dropped the question, and the program ran with no
    // message.
    // So is `x mod 2^63 == 1` (R4-CLAUDE-1), its divisor read as no constant.
    let rows = "ok(x, y, z, w) = 4 * x - 12 * w - 10 * y - 12 * z + 11 >= 0 && 4 * w + 10 * x - \
                10 * y - 11 * z - 28 >= 0 && 11 * w + 4 * x - y + 12 * z - 28 >= 0 && -8 * w - \
                5 * x + 12 * y - z + 31 >= 0";
    for (extra, printed) in [
        ("x < 9223372036854775807", "x <= 9223372036854775806\n"),
        ("x < 9223372036854775808", "x <= 9223372036854775807\n"),
        ("x < 18446744073709551616", "x <= 18446744073709551615\n"),
        (
            "x mod 9223372036854775807 == 1",
            "x mod 9223372036854775807",
        ),
        (
            "x mod 9223372036854775808 == 1",
            "x mod 9223372036854775808",
        ),
    ] {
        let src = program(&format!("{rows} && {extra};"), "x: a, y: a, z: a, w: a");
        let refusal = rejection("growth-big-bound", &src);
        assert!(refusal.contains(printed), "{extra}: {refusal}");
    }
}

#[test]
fn a_refused_question_names_the_parameters_as_written_when_other_functions_share_them() {
    // `other` and `first` bind `x` and `w` too, so elaboration renames `ok`'s parameters
    // `x@k` and `w@k`; the message names them `x` and `w`, as `ok` wrote them, in the order
    // it prints them with no other function in the unit (item NAME-at-print).
    let [first, second] = REFUSED[2].rows;
    let src = program(
        &format!(
            "ok(x, y, z, w) = {first} && {second};\nother(x) = x > 2;\nfirst(w, x1) = w > x1;"
        ),
        "x: a, y: a, z: a, w: a",
    );
    assert_eq!(
        rejection("tie-alone", &src),
        format!(
            "{}to find whole numbers that meet these \
             conditions, the checker removes one variable at a time, putting in place of the \
             conditions on it conditions on the variables left. Its next step must choose among \
             the variables `w`, `x`, `z`, `y`, which occur alike in the conditions (with the \
             same coefficients, in conditions that are alike) and share the conditions \
             `-w + 3 * x - 10 >= 0`, `3 * w - z - 10 >= 0`, `-x + 3 * y - 10 >= 0`, \
             `3 * z - y - 10 >= 0`, so only their names could order them, and the checker never \
             lets a name change an answer. The checker stopped there, with no values found and \
             none ruled out.\n  \
             [1] 1:38: the constraints: x <= 3 * y - 10 && y <= 3 * z - 10 && 3 * w >= z + 10 \
             && w <= 3 * x - 10\n  {}",
            head_in(&src),
            menu(
                "w",
                Some(("w", "x")),
                &format!("{first} && {second}"),
                [
                    "3 * w - z - 10 >= 0",
                    "3 * y - x - 10 >= 0 && 3 * z - y - 10 >= 0 && 3 * x - w - 10 >= 0"
                ]
            )
        )
    );
}

#[test]
fn a_question_whose_point_lies_past_one_splinter_is_rejected() {
    let src = program(
        "ok(x, y, z, w) = 9 * x - 4 * y - 8 * w - 3 >= 0 && 5 * x + 11 * y + 9 * w - 9 >= 0 && -7 \
         * x - 12 * y - 2 * z + 8 * w - 1 >= 0 && -9 * x + 8 * y + 7 * z >= 0 && -10 * x + 4 * y \
         - 6 * z - 4 * w + 22 >= 0;",
        "x: a, y: a, z: a, w: a",
    );
    assert_eq!(
        rejection("shadows-alone", &src),
        format!(
            "{}to find whole numbers that meet these \
             conditions, the checker removes one variable at a time, putting in place of the \
             conditions on it conditions on the variables left. Where the values a variable can \
             take have gaps, it splits the conditions into cases, one for each gap. Here the \
             only values could lie in a case that would have to be split again with as many \
             variables left as before, so the splitting need not end. The checker stopped \
             there, with no values found and none ruled out.\n  \
             [1] 1:38: the constraints: 8 * w + 4 * y <= 9 * x - 3 && 9 * w + 5 * x + 11 * y >= \
             9 && 8 * w >= 7 * x + 12 * y + 2 * z + 1 && 9 * x <= 8 * y + 7 * z && 4 * w + 10 * \
             x + 6 * z <= 4 * y + 22\n  {}",
            head_in(&src),
            menu("x", None, &REFUSED[1].rows.join(" && "), REFUSED[1].rows)
        )
    );
}

#[test]
fn a_question_over_three_names_past_one_splinter_is_decided() {
    // The question this file rejected before LIVE3 (a splinter of a splinter): over three
    // names it is now decided by `live3`, so nothing is rejected, and `ok` holds at
    // (5, 12, -7): 4 - 10 - 36 + 42 = 0, -20 + 42 - 22 = 0, 5 - 12 - 28 + 36 = 1 and
    // 10 + 36 - 21 - 24 = 1. With input 5 the call is at (5, 12, -7); with 0 at (0, 7, -2),
    // where the second row is 12 - 22 = -10.
    let src = program(
        "ok(x, y, z) = 4 - 2 * x - 3 * y - 6 * z >= 0 && -4 * x - 6 * z - 22 >= 0 && x - y + 4 \
         * z + 36 >= 0 && 2 * x + 3 * y + 3 * z - 24 >= 0;",
        "x: a, y: a + 7, z: 0 - a - 2",
    );
    for (input, out) in [("5\n", "in\n"), ("0\n", "out\n")] {
        let o = run("splinter3", &src, input, &[]);
        assert_eq!(
            (o.status, o.stdout.as_str(), o.stderr.as_str()),
            (0, out, ""),
            "{input}"
        );
    }
}

#[test]
fn a_decided_question_over_four_names_is_accepted() {
    // Four names with an equality to eliminate and unit bounds: the solver decides it.
    let src = program(
        "ok(x, y, z, w) = 0 <= x && x <= 10 && 0 <= y && y <= x && x + y + z + w == 7;",
        "x: a, y: a, z: 0, w: 7 - 2 * a",
    );
    let o = run("decided", &src, "3\n", &[]);
    assert_eq!(
        (o.status, o.stdout.as_str(), o.stderr.as_str()),
        (0, "in\n", "")
    );
}

#[test]
fn the_linear_questions_of_a_unit_scale() {
    // `n` functions of two linear tests each, every one asked whether it can hold and fail.
    let unit = |n: usize| {
        let mut src: String = (0..n)
            .map(|i| {
                format!("ok{i}(x: int, y: int) = 0 <= 3 * x + 5 * y && 2 * x - 7 * y <= {i};\n")
            })
            .collect();
        src.push_str(&program("", "x: a, y: a").replace("ok(", "ok0("));
        src
    };
    // The questions are timed alone, on a unit loaded before the timing (COMPLEXITY.md F85).
    let units: std::collections::BTreeMap<usize, _> = [64, 64 * zed_tests::scaling::FACTOR]
        .into_iter()
        .map(|m| {
            let src = unit(m);
            let program = zedc::run::load(src.as_bytes()).unwrap();
            let tokens = zedc::lex::lex_fence(&src).unwrap();
            (m, (zed_tests::deep::statements(&src), tokens, program, src))
        })
        .collect();
    zed_tests::scaling::check("the linear questions of a unit", 64, |m| {
        let (stmts, tokens, program, src) = &units[&m];
        let refused = zedc::front::linear_questions(src, tokens, stmts, program.unit());
        assert!(refused.is_empty(), "{refused:?}");
    });
}

#[test]
fn a_refused_question_through_a_call_prints_what_the_question_written_out_prints() {
    // `ok` holds `base`'s relation as one shared part (LOAD-chain-share); the refusal, its
    // cause and the constraints it prints are those of `ok` with `base`'s rows written in it.
    // But for the tie: `main` passes `ok` a local, so `ok`'s parameters join no class with
    // `base`'s, and `ok`'s call of `base` binds `base`'s canonical atoms to `ok`'s
    // (LOAD-chain-affine). The question is then over eight variables and four equalities, whose
    // structure tells every variable apart, and the solver decides it (it holds, at 5 for all
    // four) with no choice falling to a name; written over four names alike, the rows tie and
    // are refused. The answer is the same under renamings of the four names, both ways round,
    // checked below; `ok` is false at 3.
    const ARGS: &str = "x: a, y: a, z: a, w: a";
    for r in &REFUSED {
        let [first, second] = r.rows;
        let called = program(
            &format!(
                "base(x, y, z, w) = {first};\nok(x, y, z, w) = base(x: x, y: y, z: z, w: w) && \
                 {second};"
            ),
            ARGS,
        );
        let written = program(&format!("ok(x, y, z, w) = {first} && {second};"), ARGS);
        if r.name == "tie" {
            // `src` with the names x, y, z, w renamed to `to`, where they stand alone.
            let renamed = |src: &str, to: [&str; 4]| {
                let mut out = String::new();
                let cs: Vec<char> = src.chars().collect();
                for (i, &c) in cs.iter().enumerate() {
                    let alone = |j: Option<&char>| !j.is_some_and(|c| c.is_alphanumeric());
                    match "xyzw".find(c) {
                        Some(k)
                            if alone(i.checked_sub(1).map(|j| &cs[j])) && alone(cs.get(i + 1)) =>
                        {
                            out.push_str(to[k])
                        }
                        _ => out.push(c),
                    }
                }
                out
            };
            for (i, to) in [
                ["x", "y", "z", "w"],
                ["w", "z", "y", "x"],
                ["p4", "p3", "p2", "p1"],
                ["p1", "p2", "p3", "p4"],
            ]
            .into_iter()
            .enumerate()
            {
                for input in ["3\n", "5\n"] {
                    let o = run(
                        &format!("tie-called-{i}"),
                        &renamed(&called, to),
                        input,
                        &[],
                    );
                    let want = if input == "3\n" { "out\n" } else { "in\n" };
                    assert_eq!(
                        (o.status, o.stdout.as_str()),
                        (0, want),
                        "{to:?}: {}",
                        o.stderr
                    );
                }
                rejection(&format!("tie-written-{i}"), &renamed(&written, to));
            }
            continue;
        }
        let called = stated(&rejection(&format!("{}-called", r.name), &called))
            .replace("2:1: ", "1:1: ")
            .replace("2:38: ", "1:38: ");
        assert_eq!(
            unwritten(&called),
            unwritten(&stated(&rejection(
                &format!("{}-written", r.name),
                &written
            ))),
            "{}",
            r.name
        );
    }
}

#[test]
fn a_question_read_in_its_callees_coordinates_is_answered_and_printed_over_its_own_parameters() {
    // LOAD-chain-args: `ok` passes `tie` its parameters renamed, and moved by constants, so
    // its relation is read over `tie`'s parameters; what the checker prints for `ok` is what it
    // prints when `ok` states the same constraints over its own parameters, with no call.
    let [first, second] = REFUSED[2].rows;
    // `rows` with each of `x`, `y`, `z` and `w` replaced by its argument in `args`.
    let substituted = |rows: &str, args: [&str; 4]| -> String {
        let mut out = String::new();
        let mut prev = ' ';
        for ch in rows.chars() {
            match "xyzw".find(ch).filter(|_| !prev.is_alphanumeric()) {
                Some(i) => out.push_str(&format!("({})", args[i])),
                None => out.push(ch),
            }
            prev = ch;
        }
        out
    };
    // What the checker prints: the messages and their notes, without the source lines.
    let printed = |name: &str, src: &str| -> String {
        let o = run(name, src, "3\n", &[]);
        assert_eq!(o.status, 1, "{}", o.stderr);
        (o.stderr.lines())
            .map(|l| l.split_once("prog.zed:").map_or(l, |(_, rest)| rest))
            .filter(|l| {
                l.starts_with(|c: char| c.is_ascii_digit()) || l.trim_start().starts_with('[')
            })
            .collect::<Vec<_>>()
            .join("\n")
    };
    let tie = format!("tie(x, y, z, w) = {first} && {second};");
    for (i, args) in [["b", "c", "d", "a"], ["b + 1", "c", "d - 2", "a"]]
        .into_iter()
        .enumerate()
    {
        let call_body = format!(
            "tie(x: {}, y: {}, z: {}, w: {})",
            args[0], args[1], args[2], args[3]
        );
        let call = format!("ok(a, b, c, d) = {call_body};");
        let alone = format!(
            "ok(a, b, c, d) = {} && {};",
            substituted(first, args),
            substituted(second, args)
        );
        let through = printed(
            &format!("coordinates-call-{i}"),
            &program(&format!("{tie}\n{call}"), "a: a, b: a, c: a, d: a"),
        );
        let expected = printed(
            &format!("coordinates-alone-{i}"),
            &program(&format!("{tie}\n{alone}"), "a: a, b: a, c: a, d: a"),
        );
        assert_eq!(
            unwritten(&stated(&through)),
            unwritten(&stated(&expected)),
            "{call}"
        );
        assert!(through.contains("the condition of `tie`"), "{through}");
        // Passed the parameters unchanged, `ok` asks `tie`'s question and is refused too; its
        // menu rewrites the call as written, and each repair ends `ok`'s refusal. Shifted,
        // the names no longer occur alike, and `ok`'s question is decided.
        let Some(at) = through.find("the condition of `ok`") else {
            assert_eq!(i, 1, "{through}");
            continue;
        };
        let of_ok = &through[at..];
        let menu = repairs(of_ok);
        assert_eq!(menu.len(), 2, "{of_ok}");
        for r in menu {
            let def = (r.split('`').skip(1).step_by(2))
                .find(|c| {
                    c.starts_with("ok(a: int, b: int, c: int, d: int) = ")
                        && c.ends_with(&format!("{call_body};"))
                })
                .unwrap_or_else(|| panic!("no rewritten call in {r}"));
            let o = run(
                &format!("coordinates-repaired-{i}"),
                &program(&format!("{tie}\n{def}"), "a: a, b: a, c: a, d: a"),
                "3\n",
                &[],
            );
            // `tie` itself is still refused, which shows the program reached the checker.
            assert!(
                o.stderr.contains("the condition of `tie`"),
                "{def}: {}",
                o.stderr
            );
            assert!(
                !o.stderr.contains("the condition of `ok`"),
                "{def}: {}",
                o.stderr
            );
        }
    }
}

#[test]
fn a_question_refused_through_a_call_by_a_map_of_its_parameters_names_its_parameters() {
    // LOAD-chain-affine: `ok` passes `base` its `x` doubled or negated, so `base`'s relation
    // is read once, over its own atoms, and the call binds them to `ok`'s terms. The rejection
    // of `ok`'s question, its cause and constraints, are those of `ok` with `base`'s rows
    // written in it at those terms, over `ok`'s own parameters.
    const ARGS: &str = "x: a, y: a, z: a, w: a";
    let mut refused = 0;
    for r in &REFUSED[..2] {
        let [first, second] = r.rows;
        for (i, x) in ["2 * x", "0 - x"].into_iter().enumerate() {
            // `first` with each `x` replaced by `(x)`.
            let mut at = String::new();
            let mut prev = ' ';
            for ch in first.chars() {
                match ch == 'x' && !prev.is_alphanumeric() {
                    true => at.push_str(&format!("({x})")),
                    false => at.push(ch),
                }
                prev = ch;
            }
            let called = program(
                &format!(
                    "base(x, y, z, w) = {first};\nok(x, y, z, w) = base(x: {x}, y: y, z: z, w: w) \
                     && {second};"
                ),
                ARGS,
            );
            let written = program(&format!("ok(x, y, z, w) = {at} && {second};"), ARGS);
            let (o, w) = (
                run(&format!("{}-map-{i}-called", r.name), &called, "3\n", &[]),
                run(&format!("{}-map-{i}-written", r.name), &written, "3\n", &[]),
            );
            assert_eq!(
                (o.status, &o.stdout),
                (w.status, &w.stdout),
                "{x}: {}",
                o.stderr
            );
            if o.status != 1 {
                continue;
            }
            refused += 1;
            let called = stated(&rejection(&format!("{}-map-{i}-called", r.name), &called))
                .replace("2:1: ", "1:1: ")
                .replace("2:38: ", "1:38: ");
            assert!(called.contains("the condition of `ok`"), "{called}");
            assert!(!called.contains(['#', '@']), "{called}");
            assert_eq!(
                unwritten(&called),
                unwritten(&stated(&rejection(
                    &format!("{}-map-{i}-written", r.name),
                    &written
                ))),
                "{} at {x}",
                r.name
            );
        }
    }
    assert!(refused > 0, "no question refused");
}

#[test]
fn a_large_literal_keeps_a_question_that_is_refused() {
    for (name, literal) in [
        ("growth-large63", "9223372036854775808"),
        ("growth-large64", "18446744073709551616"),
    ] {
        let src = program(
            &format!(
                "ok(x, y, z, w) = 4 * x - 12 * w - 10 * y - 12 * z + 11 >= 0 && 4 * w + 10 * x - 10 * y - 11 * z - 28 >= 0 && 11 * w + 4 * x - y + 12 * z - 28 >= 0 && -8 * w - 5 * x + 12 * y - z + 31 >= 0 && x < {literal};"
            ),
            "x: a, y: a, z: a, w: a",
        );
        assert!(rejection(name, &src).contains("could not decide"));
    }
}

#[test]
fn a_refused_question_over_one_variable_names_its_moduli() {
    // Enumeration case 371, refused (it holds at 19 and 20). The variables the shadows reason
    // counts are the checker's, one for each remainder and quotient, and the reason says so
    // and names the moduli (I4.11); `a_question_whose_point_lies_past_one_splinter_is_rejected`
    // keeps the reason over four variables of the program.
    let src = program(
        "ok(x) = x >= 4 && x <= 31 && (x - 1) mod 9 <= 1 && (x - 4) mod 14 <= 4 && (x - 4) mod 27 != 23;",
        "x: a",
    );
    let printed = rejection("shadows-one-variable", &src);
    assert!(
        printed.contains(
            "The program has one variable, `x`, and the conditions read it through its \
             remainders and quotients by 9, 14 and 27; the checker gives each remainder and \
             quotient a variable of its own. Where the values a variable can take have gaps, it \
             splits the conditions into cases, one for each gap. Here the only values could lie \
             in a case that would have to be split again with as many of the checker's \
             variables left as before, so the splitting need not end. The checker stopped \
             there, with no values found and none ruled out.\n"
        ),
        "{printed}"
    );
    assert!(!printed.contains("as many variables left"), "{printed}");
}
#[test]
fn written_wide_divisors_keep_the_question() {
    let rows = "ok(x, y, z, w) = 4 * x - 12 * w - 10 * y - 12 * z + 11 >= 0 && 4 * w + 10 * x - 10 * y - 11 * z - 28 >= 0 && 11 * w + 4 * x - y + 12 * z - 28 >= 0 && -8 * w - 5 * x + 12 * y - z + 31 >= 0";
    for divisor in [
        "170141183460469231731687303715884105729",
        "340282366920938463463374607431768211457",
    ] {
        let src = program(
            &format!("{rows} && x mod {divisor} == 1;"),
            "x: a, y: a, z: a, w: a",
        );
        let got = rejection("growth-written-wide-divisor", &src);
        assert!(got.contains(divisor), "{got}");
    }
}

#[test]
#[ignore = "I4.5: record the CLI behavior of kept powers without claiming they are handled"]
fn pncx_kept_number_cli() {
    let rows = "ok(x, y, z, w) = 4 * x - 12 * w - 10 * y - 12 * z + 11 >= 0 && 4 * w + 10 * x - 10 * y - 11 * z - 28 >= 0 && 11 * w + 4 * x - y + 12 * z - 28 >= 0 && -8 * w - 5 * x + 12 * y - z + 31 >= 0";
    let mut rejected = true;
    for extra in [
        "x < 2^200",
        "x < 2^100000",
        "x mod 2^200 == 1",
        "x mod 170141183460469231731687303715884105728 == 1",
        "x mod (2^128 + 1) == 1",
    ] {
        let src = program(&format!("{rows} && {extra};"), "x: a, y: a, z: a, w: a");
        let o = run("kept-number-cli", &src, "3\n", &[]);
        println!(
            "KEPT_CLI {extra}: status={} stdout={:?} stderr={:?}",
            o.status, o.stdout, o.stderr
        );
        rejected &= o.status == 1 && o.stdout.is_empty();
    }
    assert!(
        rejected,
        "I4.5 remains: at least one question was silently dropped"
    );
}
