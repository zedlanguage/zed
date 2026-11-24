//! The type printer writes parentheses exactly where the grammar needs them to keep a type's
//! meaning (author P191). The grammar has no precedence table: precedence comes from the
//! layering of the rules of DESIGN.md sec:grammar, `Arrow` → `TypeUnion` → `TypeDiff`/`TypeOr`
//! → `TypeAnd` → `TypeNot` → `TypePostfix` → `TypePrimary`, where a `~X` alternative passes
//! through to the next layer. A text in a position needs a pair exactly when the rule that
//! produces it cannot be reached from the rule the position expects through `~` alternatives
//! alone.
//!
//! Three tests: the kernel printer's places checked against that reachability, computed from
//! the grammar the parser reads; and, over generated types, the round trip (the printed text
//! parses back to the type) and minimality (deleting any one pair of parentheses from the
//! printed text either fails to parse or gives another type). Minimality also catches what the
//! layering alone misses: PEG ordered choice, as `(A, B) -> V` read as two parameters, and
//! lookaheads, as `TypeUnion = ~TypeDiff !('|' | '&')`.

use std::collections::HashSet;

use zed_kernel::types::rec::{Def, Expr, Group};
use zed_kernel::types::{TextPlace, Type as KType};
use zed_tests::seed::Rng;
use zedc::check::read::parse_type;
use zedc::check::ty::Ty;
use zedc::lex::lex_fence;
use zedc::parse::{Grammar, TOP, grammar, marked_rule, parse};

use super::printed::stated;

/// The rules reachable from rule `r` through `~` alternatives alone, `r` among them: the
/// rules whose text stands where `r` is expected with no parentheses. A visited set bounds the
/// walk; the stack is explicit.
fn reach(g: &Grammar, r: usize) -> HashSet<usize> {
    let mut seen = HashSet::from([r]);
    let mut work = vec![r];
    while let Some(r) = work.pop() {
        for alt in g.rules[r].alts.iter().filter(|a| a.pass) {
            let m = marked_rule(&alt.expr).expect("a `~` alternative marks a rule");
            if seen.insert(m) {
                work.push(m);
            }
        }
    }
    seen
}

fn rule(g: &Grammar, name: &str) -> usize {
    g.rule(name)
        .unwrap_or_else(|| panic!("the grammar has no rule `{name}`"))
}

/// The kernel printer's places, each with the rules the grammar expects there, any one of which
/// may produce the text: a whole type is an `Arrow` (`Type = Arrow TypeFacet* …`); an operand
/// of `|` stands on either side, as the right one (`TypeOr '|' TypeAnd`) at the most; an operand
/// of `&` likewise (`TypeAnd '&' TypeNot`); the left of `\` is `TypeDiff` or `TypeNot`
/// (`TypeDiff '\\' TypeNot | TypeNot '\\' TypeNot`); an operand of any connective is a
/// `TypeNot`; a key (`TypeNot '->' Arrow`) and a bound (`TypeNot '..' TypeNot`) are `TypeNot`s,
/// since `|`, `&` and `\` bind tighter than `->` (author P222); the type after `is` (`IsTest`,
/// `IsPat`) is a `TypeUnion`.
const PLACES: [(TextPlace, &[&str]); 8] = [
    (TextPlace::Any, &["Arrow"]),
    (TextPlace::Union, &["TypeAnd"]),
    (TextPlace::And, &["TypeNot"]),
    (TextPlace::DiffLeft, &["TypeDiff", "TypeNot"]),
    (TextPlace::Prim, &["TypeNot"]),
    (TextPlace::Key, &["TypeNot"]),
    (TextPlace::Bound, &["TypeNot"]),
    (TextPlace::Is, &["TypeUnion"]),
];

/// Kernel types of each form, each with its text and the rule that produces that text.
fn forms() -> Vec<(KType, &'static str, &'static str)> {
    let a = KType::atom("a");
    vec![
        (KType::int(), "int", "TypeName"),
        (
            KType::atom_with("a", &KType::tuple(vec![KType::int()])),
            "#a(int)",
            "AtomApply",
        ),
        (
            KType::tuple(vec![KType::int(), KType::bool()]),
            "(int, bool)",
            "TupleType",
        ),
        (&KType::int() | &a, "int | #a", "TypeOr"),
        (&KType::top() - &a, "_ \\ #a", "TypeDiff"),
        (
            KType::partial(KType::int(), KType::bool()),
            "int ->? bool",
            "Arrow",
        ),
    ]
}

/// Where the kernel printer departs from reachability, and why. Associativity: an operand of
/// `|` that is itself a union reads the same with or without the pair, so none is written, and
/// likewise for `&`. Ordered choice: a tuple as a key reads as the parameters, since `Arrow`
/// tries `ArrowParams` first, so `((A, B)) -> V` keeps its pair.
fn departs(place: TextPlace, form: &str) -> Option<bool> {
    match (place, form) {
        (TextPlace::Union, "TypeOr") | (TextPlace::And, "TypeAnd") => Some(false),
        (TextPlace::Key, "TupleType") => Some(true),
        _ => None,
    }
}

/// Each kernel form at each place is parenthesized exactly when the rule that produces it is
/// not reachable from a rule the place expects, but for the departures [`departs`] names.
#[test]
fn the_kernel_printer_parenthesizes_where_the_grammar_layering_needs_it() {
    let g = grammar();
    let mut wrong = Vec::new();
    for (k, alone, form) in forms() {
        assert_eq!(k.surface_by_name(TextPlace::Any).root, alone, "{form}");
        for (place, expected) in PLACES {
            let reached = expected
                .iter()
                .any(|e| reach(g, rule(g, e)).contains(&rule(g, form)));
            let wrap = departs(place, form).unwrap_or(!reached);
            let printed = k.surface_by_name(place).root;
            let want = if wrap {
                format!("({alone})")
            } else {
                alone.to_string()
            };
            if printed != want {
                wrong.push(format!(
                    "{form} `{alone}` at {place:?}: `{printed}`, not `{want}`"
                ));
            }
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

const LEAVES: [&str; 12] = [
    "int",
    "bool",
    "f64",
    "String",
    "#a",
    "#b",
    "0",
    "1",
    "_",
    "()",
    "int[0..9]",
    "rat",
];

/// The text of a random type `depth` levels deep at most, each operand in its own parentheses,
/// so that it reads as built whatever the printer would write.
fn generated(rng: &mut Rng, depth: usize) -> String {
    if depth == 0 || rng.below(4) == 0 {
        return LEAVES[rng.below(LEAVES.len())].to_string();
    }
    let sub = |rng: &mut Rng| format!("({})", generated(rng, depth - 1));
    match rng.below(15) {
        0 => format!("{} | {}", sub(rng), sub(rng)),
        1 => format!("{} & {}", sub(rng), sub(rng)),
        2 => format!("{} \\ {}", ["int", "rat", "String"][rng.below(3)], sub(rng)),
        3 => format!("({}, {})", sub(rng), sub(rng)),
        4 => format!("({},)", sub(rng)),
        5 => format!("#box({})", sub(rng)),
        6 => format!("#pair({}, {})", sub(rng), sub(rng)),
        7 => format!("{} -> {}", sub(rng), sub(rng)),
        8 => format!("({}, {}) -> {}", sub(rng), sub(rng), sub(rng)),
        9 => format!("(x: {}) -> {}", sub(rng), sub(rng)),
        10 => format!("{} ->? {}", sub(rng), sub(rng)),
        11 => {
            // A bound pair `L .. U` needs `L` within `U` and apart from it.
            let lower = sub(rng);
            format!("{lower} .. ({lower} | {}) -> {}", sub(rng), sub(rng))
        }
        12 => format!("!{}", sub(rng)),
        13 => "((T) -> T for T in int | f64)".to_string(),
        _ => format!(
            "(({}) -> {}) & ((x: {}) -> {})",
            sub(rng),
            sub(rng),
            sub(rng),
            sub(rng)
        ),
    }
}

/// The spans of the pairs of parentheses in `text`, outside string literals.
fn pairs(text: &str) -> Vec<(usize, usize)> {
    let mut open = Vec::new();
    let mut out = Vec::new();
    let mut quoted = false;
    for (i, c) in text.char_indices() {
        match c {
            '"' => quoted = !quoted,
            '(' if !quoted => open.push(i),
            ')' if !quoted => out.push((open.pop().expect("balanced"), i)),
            _ => {}
        }
    }
    out
}

/// Whether `a` and `b` are one type: the same as type syntax states them, or each a subtype of
/// the other with one printed text. The reader keeps a type as written, the printer in its own
/// order and form, so `(bool, bool) | (1, f64)` and `(1, f64) | (bool, bool)` read apart.
/// The reader keeps the other members of a union that holds `_`, which the printer drops,
/// since `_` absorbs them (A92); [`stated`] drops them too, so `#box((_ .. (_ | 1) -> #a) | (0
/// .. (0 | _) -> rat))` reads back as itself, though the checker refuses to compare two
/// functions at one place of a payload with two others not all equal. Subtyping alone does not
/// tell payloads apart, `#box(#pair(f64, bool))` from `#box(#pairf64, bool)`, so the texts must
/// agree too.
fn same(a: &Ty, b: &Ty) -> bool {
    stated(a) == stated(b) || (a.subtype(b) && b.subtype(a) && a.to_string() == b.to_string())
}

/// Types generated at random, each printed: the text parses back to the type (round trip), and
/// deleting any one pair of its parentheses either fails to parse or gives another type
/// (minimality). The forms the printed texts hold are counted, and a form no draw printed is
/// printed by the text [`FORMS`] builds for it.
#[test]
fn printed_types_read_back_and_hold_no_parentheses_the_grammar_does_not_need() {
    read_back_round(zed_tests::seed::seed(
        "printed_types_read_back_and_hold_no_parentheses_the_grammar_does_not_need",
    ));
}

/// The round trip and minimality test above on seeds that drew types whose subtype tests
/// put the leaf part of one tuple length, then a tuple of another length, in one search; the
/// search's index of the first was read for the second, and `candidates` in zed-kernel's
/// `types::empty` indexed a column the index did not have
/// (FAIL-kernel-candidates-key-past-columns).
#[test]
fn printed_types_read_back_on_seeds_that_met_one_index_for_two_tuple_lengths() {
    for seed in [
        15276803015084382426_u64,
        17195149157679997797,
        6869086033364754509,
    ] {
        read_back_round(seed);
    }
}

/// The round trip and minimality test above on seed 76, which drew `a` =
/// `((rat) ->? (_)) | ((#a) ->? (_))` in `a .. (a & (a | v)) -> b`: the reader left the meet
/// `(rat | (#a ->? _) | (rat ->? _) | (#a -> bool)) ->? rat` unnarrowed, within neither side,
/// until it narrowed parameter types pairing several function types (TYPES-meet-fns-indexed).
#[test]
fn printed_types_read_back_on_a_seed_that_met_unions_of_function_types() {
    read_back_round(76);
}

/// The round trip and minimality test above on seeds that failed it
/// (FAIL-parens-wrong-is-empty-seed). Seed 24 printed `(0 | ((T -> T) & (f64 -> _) for T in int |
/// f64)) -> #notFound`, a pair too many around the intersection in a key union, since inside
/// the key's pair the clause may go to the end of the union. Seed 306 drew `(rat .. (rat | _) ->
/// String) | (String .. (String | _) -> 0)` in a payload, whose `rat | _` reads back as `_`,
/// and the checker refuses to compare two functions at one place of a payload when they are
/// not all equal. Seed 7108425237053606485 printed no difference in its 3000 draws, which the
/// text [`FORMS`] builds for it prints.
#[test]
fn printed_types_read_back_on_seeds_that_met_a_clause_in_a_key_union() {
    for seed in [24_u64, 306, 7108425237053606485] {
        read_back_round(seed);
    }
}

/// The round trip and minimality test above on seeds whose types held two members that differ
/// only inside a union holding `_`, which the printer wrote as one text twice
/// (FAIL-print-absorbed-members-twice): seed 1661 drew `#box(0 | _) .. (#box(0 | _) | #box(_))
/// -> bool`, seed 7306999953964951699 `(bool | _,) | (_,)`, and seed 2630 two functions of
/// bounded arrows `_ .. (_ | ()) -> String` and `_ .. (_ | #a) -> String`.
#[test]
fn printed_types_read_back_on_seeds_that_held_members_equal_once_underscore_absorbs() {
    for seed in [1661_u64, 2630, 7306999953964951699] {
        read_back_round(seed);
    }
}

/// A union of members that differ only inside a union holding `_` prints each once, as the
/// reader reads the text, and the text reads back as the type
/// (FAIL-print-absorbed-members-twice): `_` holds every value, so `0 | _` is `_` (A92), and
/// `#box(0 | _) | #box(_)` is `#box(_)`.
#[test]
fn members_equal_once_underscore_absorbs_print_once() {
    for (text, expected) in [
        ("#box((0) | (_)) | #box(_)", "#box(_)"),
        ("#box(_) | #box((0) | (_))", "#box(_)"),
        ("((0, 0 | _)) | ((0, _))", "(0, _)"),
        ("((((bool) | (_)),)) | (((_),))", "(_,)"),
        (
            "(#box(0 | _)) .. ((#box(0 | _)) | (#box(_))) -> bool",
            "#box(_) -> bool",
        ),
        (
            "((0 | _) -> bool, int) | (_ -> bool, int)",
            "(_ -> bool, int)",
        ),
        ("#box((0 | _) -> bool) | #box(_ -> bool)", "#box(_ -> bool)"),
    ] {
        let t = parse_type(text).unwrap();
        let back = parse_type(&t.to_string()).unwrap();
        assert_eq!(t.to_string(), expected, "{text}");
        assert!(same(&t, &back), "{text} prints {t}, read back as {back}");
    }
}

/// The smallest pair seen for FAIL-kernel-candidates-key-past-columns: the printed type of
/// seed 6869086033364754509 and one deletion the minimality check tries. The two are
/// different types (the payload of `#pair` is the empty tuple in one, a pair in the other).
#[test]
fn a_payload_of_the_empty_tuple_and_one_of_a_pair_are_told_apart() {
    let a = parse_type("#box((#pair(), 1,))").unwrap();
    let b = parse_type("#box((#pair((), 1),))").unwrap();
    assert!(!same(&a, &b), "{a} and {b}");
}

/// The random draws of [`read_back_round`], about seven of which print ` \ ` in a seed.
const DRAWS: usize = 3000;

/// The forms the printed texts of [`read_back_round`] must hold, each with a text built to
/// print it (checked alone by [`each_text_built_for_a_form_prints_it`]). A seed may print a
/// form rarely, as ` \ `, which the printer simplifies in most differences (no ` \ ` in 3000
/// draws for seed 7108425237053606485, FAIL-parens-wrong-is-empty-seed), so a form the draws
/// did not print is printed by its text, and no number of draws is relied on
/// (PROOF-test-coverage-constructive).
const FORMS: [(&str, &str); 9] = [
    (" -> ", "(int) -> bool"),
    (" ->? ", "(int) ->? bool"),
    (" .. ", "(int | #a) .. (int | #a | #b) -> int"),
    (" | ", "int | #a"),
    (" & ", "((int) -> int) & ((f64) -> f64)"),
    (" \\ ", "(int \\ 3) -> int"),
    (" for ", "((T) -> T for T in int | f64)"),
    ("#box(", "#box(int)"),
    (",)", "((int,)) -> int"),
];

/// Checks the type `t` read from `text` and printed as `printed`: the printed text parses
/// back to `t` (round trip), and deleting any one pair of its parentheses either fails to
/// parse or gives another type (minimality). Each failure is pushed to `wrong`.
fn check_printed(text: &str, t: &Ty, printed: &str, wrong: &mut Vec<String>) {
    match parse_type(printed) {
        Ok(back) if same(&back, t) => {}
        Ok(_) => wrong.push(format!(
            "`{text}` prints `{printed}`, read back as another type"
        )),
        Err(e) => wrong.push(format!(
            "`{text}` prints `{printed}`, which does not parse: {e}"
        )),
    }
    for (a, b) in pairs(printed) {
        let less = format!(
            "{}{}{}",
            &printed[..a],
            &printed[a + 1..b],
            &printed[b + 1..]
        );
        if parse_type(&less).is_ok_and(|back| same(&back, t)) {
            wrong.push(format!(
                "`{text}` prints `{printed}`; `{less}` reads the same"
            ));
        }
    }
}

/// Each text of [`FORMS`] reads, prints its form, and passes the round trip and minimality
/// checks.
#[test]
fn each_text_built_for_a_form_prints_it() {
    let mut wrong = Vec::new();
    for (form, text) in FORMS {
        let t = parse_type(text).unwrap_or_else(|e| panic!("`{text}`: {e}"));
        let printed = t.to_string();
        assert!(
            printed.contains(form),
            "`{text}` prints `{printed}`, no `{form}`"
        );
        check_printed(text, &t, &printed, &mut wrong);
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// One round of [`printed_types_read_back_and_hold_no_parentheses_the_grammar_does_not_need`]
/// with the random generator seeded by `seed`: [`DRAWS`] random types, then, for each form of
/// [`FORMS`] none of them printed, the text built to print it, checked as the draws are.
/// Fails when a form is still not printed, which happens only when the printer no longer
/// writes it.
fn read_back_round(seed: u64) {
    let mut rng = Rng::new(seed);
    let mut wrong = Vec::new();
    let mut read = 0;
    let mut seen = HashSet::new();
    let mut forms = FORMS.map(|(f, _)| (f, 0usize));
    for _ in 0..DRAWS {
        let text = generated(&mut rng, 3);
        let Ok(t) = parse_type(&text) else { continue };
        let printed = t.to_string();
        if !seen.insert(printed.clone()) {
            continue;
        }
        read += 1;
        for (f, n) in forms.iter_mut() {
            *n += usize::from(printed.contains(*f));
        }
        check_printed(&text, &t, &printed, &mut wrong);
    }
    eprintln!("{read} distinct types read: {forms:?}");
    let mut built = Vec::new();
    for ((form, n), (_, text)) in forms.iter().zip(FORMS) {
        if *n > 0 {
            continue;
        }
        let t = parse_type(text).unwrap_or_else(|e| panic!("`{text}`: {e}"));
        let printed = t.to_string();
        assert!(
            printed.contains(form),
            "`{form}` is not printed: `{text}` prints `{printed}`"
        );
        check_printed(text, &t, &printed, &mut wrong);
        built.push(*form);
    }
    eprintln!("printed only by the texts built for them: {built:?}");
    assert!(
        wrong.is_empty(),
        "{} of {read}:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
}

/// Hand-picked cases of the rule, each with its printed text: a function of one positional
/// parameter is written `K -> R`, its key parenthesized only where the grammar needs it.
#[test]
fn function_types_print_with_exactly_the_parentheses_the_grammar_needs() {
    let cases = [
        ("(int) -> int", "int -> int"),
        ("int -> int", "int -> int"),
        // DESIGN's `g(positional c: bool) = if c { 1 } else { 2 }`: `|` binds tighter than
        // `->`, so the union result needs no pair either.
        ("(bool) -> 1 | 2", "bool -> 1 | 2"),
        ("((int) -> int) -> int", "(int -> int) -> int"),
        ("(int) -> (int) -> int", "int -> int -> int"),
        ("((int, int)) -> int", "((int, int)) -> int"),
        ("(int, int) -> int", "(int, int) -> int"),
        ("((int,)) -> int", "(int,) -> int"),
        ("(()) -> int", "(()) -> int"),
        ("() -> int", "() -> int"),
        ("(int | #a) -> int", "(int | #a) -> int"),
        ("(int \\ 3) -> int", "(int \\ 3) -> int"),
        (
            "((int -> int) & (rat -> rat)) ->? int",
            "((int -> int) & (rat -> rat)) ->? int",
        ),
        (
            "(int | #a) ..(int | #a | #b) -> int",
            "(int | #a) .. (int | #a | #b) -> int",
        ),
        (
            "(int) -> int | #box((int) -> int)",
            "int -> int | #box(int -> int)",
        ),
        ("((int) -> int) | String", "String | (int -> int)"),
        ("((int) -> int, bool)", "(int -> int, bool)"),
        (
            "((int) -> int) & ((f64) -> f64)",
            "(int -> int) & (f64 -> f64)",
        ),
        ("(x: int) -> int", "(x: int) -> int"),
        ("((T) -> T for T in int | f64)", "T -> T for T in int | f64"),
        (
            "(((T) -> T for T in int), bool)",
            "(T -> T for T in int, bool)",
        ),
        (
            "(int) -> ((T) -> T for T in int)",
            "int -> (T -> T for T in int)",
        ),
        // An intersection of arrows in a union where a whole type stands leaves its bounds
        // clause to the end of the union, and needs no pair; elsewhere it keeps both.
        (
            "(((T) -> T for T in int | f64)) & ((f64) -> (_)) | rat",
            "rat | (T -> T) & (f64 -> _) for T in int | f64",
        ),
        (
            "((((T) -> T for T in int | f64)) & ((f64) -> (_)) | rat, bool)",
            "(rat | (T -> T) & (f64 -> _) for T in int | f64, bool)",
        ),
        (
            "(int) -> ((((T) -> T for T in int | f64)) & ((f64) -> (_)) | rat)",
            "int -> rat | ((T -> T) & (f64 -> _) for T in int | f64)",
        ),
        (
            "(((T) -> T for T in int)) & ((f64) -> (_)) | (((U) -> U for U in f64)) & ((rat) -> (_))",
            "(T -> T) & (f64 -> _) | (U -> U) & (rat -> _) for T in int, U in f64",
        ),
        // A union as a key is parenthesized, and inside the pair a whole type stands
        // (`GroupType = '(' Type ')'`), so the clause goes once to the end of the union there
        // too, before the `)` (FAIL-parens-wrong-is-empty-seed).
        (
            "((rat) | ((((T) -> T for T in int | f64)) & ((f64) -> (_)))) -> int",
            "(rat | (T -> T) & (f64 -> _) for T in int | f64) -> int",
        ),
        (
            "((rat) | ((((T) -> T for T in int | f64)) & ((f64) -> (_)))) ->? int",
            "(rat | (T -> T) & (f64 -> _) for T in int | f64) ->? int",
        ),
        (
            "((int) -> ((rat) | ((((T) -> T for T in int | f64)) & ((f64) -> (_))))) -> int",
            "(int -> rat | ((T -> T) & (f64 -> _) for T in int | f64)) -> int",
        ),
        // The clause at the end bounds the members before it too, so it takes a name none of
        // their clauses wrote: `for T` twice does not read. The partial arrow keeps its `->?`
        // (FAIL-main-red-exact-domain): `_ -> String | #notFound` is exact, another type.
        (
            "((T) -> T for T in int | f64) | (((T) -> T for T in int | f64)) & ((_) ->? (String))",
            "(T -> T for T in int | f64) | (U -> U) & (_ ->? String) for U in int | f64",
        ),
    ];
    let mut wrong = Vec::new();
    for (text, want) in cases {
        let t: Ty = parse_type(text).unwrap_or_else(|e| panic!("{text}: {e}"));
        let printed = t.to_string();
        if printed != want {
            wrong.push(format!("`{text}` prints `{printed}`, not `{want}`"));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
/// Whether the pair of parentheses at `a` and `b` in `text` groups: it is not a call's or an
/// atom payload's (`#box(int)`), not the empty tuple `()`, and holds no comma of its own, which
/// would make it a tuple (`(int,)`, `(int, bool)`). Deleting any other pair changes the tokens,
/// not the grouping.
fn grouping(text: &str, a: usize, b: usize) -> bool {
    let called = text[..a]
        .chars()
        .next_back()
        .is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '\'');
    let mut depth = 0usize;
    let comma = text[a + 1..b].chars().any(|c| {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            _ => {}
        }
        c == ',' && depth == 0
    });
    !called && b > a + 1 && !comma
}

/// The parse tree of `text` as a type, written out with each grouping pair taken away: a
/// `GroupType`, `(T)`, stands for `T`, and a node that is all one child, a `~` alternative or
/// a `Type` with no facet, for that child. So two texts have one shape exactly when they are
/// one tree but for grouping pairs; none if `text` does not parse. Each node is entered once,
/// from a stack.
fn shape(text: &str) -> Option<String> {
    let tokens = lex_fence(text).ok()?;
    let tree = parse(text, &tokens, "Type", TOP).ok()?;
    enum Item {
        Node(usize),
        Token(usize),
        Close,
    }
    let mut out = String::new();
    let mut todo = vec![Item::Node(tree.root)];
    while let Some(item) = todo.pop() {
        let mut n = match item {
            Item::Token(i) => {
                out += " ";
                out += &text[tokens[i].span.start..tokens[i].span.end];
                continue;
            }
            Item::Close => {
                out += ")";
                continue;
            }
            Item::Node(n) => n,
        };
        loop {
            let node = &tree.nodes[n];
            match node.kids[..] {
                [k] if tree.name(n) == "GroupType" => n = k,
                [k] if (tree.nodes[k].start, tree.nodes[k].end) == (node.start, node.end) => n = k,
                _ => break,
            }
        }
        let node = &tree.nodes[n];
        out += &format!(" ({}/{}", tree.name(n), node.alt);
        // Its own tokens and its children, in the order of the text.
        let mut items = Vec::new();
        let mut kids = node.kids.iter().peekable();
        let mut at = node.start;
        while at < node.end {
            match kids.peek() {
                Some(&&k) if tree.nodes[k].start == at => {
                    items.push(Item::Node(k));
                    at = tree.nodes[k].end;
                    kids.next();
                }
                _ => {
                    items.push(Item::Token(at));
                    at += 1;
                }
            }
        }
        todo.push(Item::Close);
        todo.extend(items.into_iter().rev());
    }
    Some(out)
}

/// What is wrong with `printed` as the text of the type `want`: it reads as another type or
/// not at all (round trip), or a grouping pair of its parentheses can go and leave the same
/// parse tree but for grouping pairs (minimality, [`shape`]). A kernel printer writes a type in
/// its own form (a canonical union order), so the round trip compares by meaning, each side a
/// subtype of the other. The deletion compares the trees, not what they read as: a group
/// printer writes a part whose meaning the whole does not depend on, as `F` in `rat \ F` for a
/// function type `F`, and a part that is empty whatever its grouping (`(#b,) & (#a,)`); the
/// reader takes such parts away, so a comparison by meaning would call any pair in them
/// needless.
fn misprinted(printed: &str, want: &Ty) -> Vec<String> {
    let back = match parse_type(printed) {
        Ok(back) => back,
        Err(e) => return vec![format!("`{printed}` does not parse: {e}")],
    };
    let mut wrong = Vec::new();
    if !(back.subtype(want) && want.subtype(&back)) {
        wrong.push(format!("`{printed}` reads as another type"));
    }
    let tree = shape(printed);
    for (a, b) in pairs(printed) {
        if !grouping(printed, a, b) {
            continue;
        }
        let less = format!(
            "{}{}{}",
            &printed[..a],
            &printed[a + 1..b],
            &printed[b + 1..]
        );
        if shape(&less).is_some() && shape(&less) == tree {
            wrong.push(format!("`{printed}`: `{less}` parses the same"));
        }
    }
    wrong
}

/// A kernel type built by [`kernel_generated`], with the text it is built from, each operand
/// in parentheses.
struct Built {
    t: KType,
    text: String,
}

/// A kernel type built at random, `depth` levels deep at most, from one-token leaves (a leaf
/// written twice is then never named by a definition) and every constructor the printer has a
/// form for. Two readings of the reader stand apart from the printer, and the types that meet
/// them are not built:
/// - a part that comes out empty (`int & String`) is replaced by a leaf, since the kernel
///   simplifies an arrow or tuple over an empty part (`Never -> V`) where the reader keeps it;
/// - no complement or difference: the reader takes `_` as the unknown type, so `_ \ X` reads
///   as `_`, and a difference the kernel keeps is one from `_`; the place of `\` is checked
///   against the grammar by the first test of this file.
///
/// - no `&` of two function types: the reader takes it as an overload, the arrows of one
///   function (DESIGN.md sec:type_language, "Relation to semantic subtyping" (2)), while the
///   kernel's `&` is the meet of the two sets. The meet of two arrows is built, and written as
///   the one arrow it is: `(a -> b) & ((a | v) ->? b)` as `a .. (a & (a | v)) -> b`.
///
/// Meets of any two types, unions of a type with a part of it, and upper bounds `L | U` that
/// hold `L` are built, as they are since rows FAIL-types-meet-function-union and
/// FAIL-types-tuple-subtype were fixed.
fn kernel_generated(rng: &mut Rng, depth: usize) -> Built {
    kernel_generated_arrow(rng, depth).0
}

/// [`kernel_generated`], and whether the text is a function type, whose `&` with another
/// would read as an overload.
fn kernel_generated_arrow(rng: &mut Rng, depth: usize) -> (Built, bool) {
    let leaf = |rng: &mut Rng| {
        let (t, text) = [
            (KType::int(), "int"),
            (KType::bool(), "bool"),
            (KType::f64(), "f64"),
            (KType::string(), "String"),
            (KType::rat(), "rat"),
            (KType::atom("a"), "#a"),
            (KType::atom("b"), "#b"),
            (KType::top(), "_"),
            (KType::tuple(vec![]), "()"),
        ]
        .into_iter()
        .nth(rng.below(9))
        .expect("a leaf");
        let text = text.to_string();
        (Built { t, text }, false)
    };
    if depth == 0 || rng.below(4) == 0 {
        return leaf(rng);
    }
    let mut sub = || {
        let (b, arrow) = kernel_generated_arrow(rng, depth - 1);
        let b = Built {
            text: format!("({})", b.text),
            ..b
        };
        (b, arrow)
    };
    let ((a, a_arrow), (b, b_arrow), (v, _)) = (sub(), sub(), sub());
    let (at, bt, vt) = (&a.text, &b.text, &v.text);
    let built = |t: KType, text: String| (Built { t, text }, false);
    let arrow = |t: KType, text: String| (Built { t, text }, true);
    let out = match rng.below(11) {
        0 => built(&a.t | &b.t, format!("{at} | {bt}")),
        1 if a_arrow && b_arrow => return leaf(rng),
        1 => built(&a.t & &b.t, format!("{at} & {bt}")),
        2 => built(
            KType::tuple(vec![a.t.clone(), b.t.clone(), v.t.clone()]),
            format!("({at}, {bt}, {vt})"),
        ),
        3 => built(
            KType::tuple(vec![a.t.clone(), b.t.clone()]),
            format!("({at}, {bt})"),
        ),
        4 => built(KType::tuple(vec![a.t.clone()]), format!("({at},)")),
        5 => built(
            KType::atom_with("box", &KType::tuple(vec![a.t.clone()])),
            format!("#box({at})"),
        ),
        6 => built(
            KType::atom_with("pair", &KType::tuple(vec![a.t.clone(), b.t.clone()])),
            format!("#pair({at}, {bt})"),
        ),
        7 => arrow(
            KType::exact(a.t.clone(), b.t.clone()),
            format!("{at} -> {bt}"),
        ),
        8 => arrow(
            KType::partial(a.t.clone(), b.t.clone()),
            format!("{at} ->? {bt}"),
        ),
        // Data types met mostly come out empty or as one side, so arrows are met here too. The
        // meet is the functions with `a ⊆ dom ⊆ a & (a | v)` and values in `b`. The upper bound
        // holds `a`, as a program's `L .. U` must: where `a` is not within it, the meet is
        // empty, which the kernel cannot always show (`a` a payload holding a function), and
        // the reader refuses the text. An `a` that holds a function is drawn too: where the
        // reader does not prove a meet of functions empty, it keeps both arrows, a meet within
        // neither side, so `a & (a | v)` was not found within `a`, and such an `a` was not
        // drawn until the reader proved these meets empty or one side
        // (FAIL-types-meet-fn-kept-not-within: `(#pair(#b, _) -> f64) & (_ -> ())`, a domain of
        // the unknown; `(rat ->? #pair(int, ())) & ((rat .. (rat | int) -> bool) -> ((),))`, a
        // function type of two domain bounds; more in
        // `judgments::a_meet_of_functions_kept_before_is_within_each_side` of l01_23).
        // An `a` whose meet with `a | v` pairs more than one function type is drawn too, since
        // the reader narrows such a parameter type (TYPES-meet-fns-indexed, COMPLEXITY.md F234);
        // before, it was not drawn, as seed 76's `((rat) ->? (_)) | ((#a) ->? (_))`, which the
        // reader left unnarrowed.
        9 => arrow(
            &KType::exact(a.t.clone(), b.t.clone()) & &KType::partial(&a.t | &v.t, b.t.clone()),
            format!("{at} .. ({at} & ({at} | {vt})) -> {bt}"),
        ),
        // A bound pair `L .. U` needs `L` within `U`: the upper bound is the union of `L` with
        // another type.
        _ => arrow(
            KType::morphism(a.t.clone(), &a.t | &b.t, v.t.clone()),
            format!("{at} .. ({at} | {bt}) -> {vt}"),
        ),
    };
    if out.0.t.is_empty() { leaf(rng) } else { out }
}

/// The kernel's surface printer (crates/zed-kernel/src/types/print.rs) over kernel types built
/// at random: each printed text reads back as the type (round trip), and no grouping pair of
/// its parentheses can go (minimality). Negative controls: a text with a pair too many and one
/// with a pair too few are each caught, and a tuple's or payload's pair is not taken for one.
/// A round trip the checker refuses for unpaired functions (COMPLEXITY.md F124) is counted, not
/// compared, where the checker gives that cause both ways.
#[test]
fn the_kernel_printer_reads_back_and_holds_no_parentheses_the_grammar_does_not_need() {
    let want = parse_type("(int -> int) | bool").unwrap();
    assert_eq!(
        misprinted("(int -> int) | (bool)", &want),
        ["`(int -> int) | (bool)`: `(int -> int) | bool` parses the same"]
    );
    assert_eq!(
        misprinted("int -> int | bool", &want),
        ["`int -> int | bool` reads as another type"]
    );
    assert!(misprinted("bool | (int -> int)", &want).is_empty());
    let payload = parse_type("#box((int,), ())").unwrap();
    assert!(misprinted("#box((int,), ())", &payload).is_empty());
    // The seed goes in the failure message too: `seed` writes its line to standard error
    // directly, which the test harness does not capture, so a merge log does not show it.
    let seed = zed_tests::seed::seed(
        "the_kernel_printer_reads_back_and_holds_no_parentheses_the_grammar_does_not_need",
    );
    let mut rng = Rng::new(seed);
    let (mut wrong, mut read, mut seen, mut unpaired) = (Vec::new(), 0, HashSet::new(), 0);
    let mut forms = KERNEL_FORMS.map(|(f, _)| (f, 0usize));
    for _ in 0..3000 {
        let Built { t: k, text } = kernel_generated(&mut rng, 3);
        let printed = k.surface();
        if !printed.exact || !printed.defs.is_empty() || !seen.insert(printed.root.clone()) {
            continue;
        }
        read += 1;
        for (f, n) in forms.iter_mut() {
            *n += usize::from(printed.root.contains(*f));
        }
        unpaired += usize::from(kernel_read_back(&text, &printed.root, &mut wrong));
    }
    // A refusal for unpaired functions is counted only where `kernel_read_back` finds that
    // cause, the checker's own message, both ways; no count of them is asserted, as their
    // number follows the draws (PROOF-test-count-thresholds).
    eprintln!("{read} distinct types read, {unpaired} refused for unpaired functions: {forms:?}");
    // A form the draws did not print is printed by the type built for it, checked as the
    // draws are.
    for ((form, n), (_, build)) in forms.iter().zip(KERNEL_FORMS) {
        if *n > 0 {
            continue;
        }
        let Built { t, text } = build();
        let printed = t.surface();
        assert!(
            printed.exact && printed.defs.is_empty() && printed.root.contains(form),
            "`{form}` is not printed: `{text}` prints `{}` (ZED_TEST_SEED={seed})",
            printed.root
        );
        assert!(
            !kernel_read_back(&text, &printed.root, &mut wrong),
            "`{text}` (ZED_TEST_SEED={seed})"
        );
        eprintln!("`{form}` printed only by `{text}`");
    }
    assert!(
        wrong.is_empty(),
        "ZED_TEST_SEED={seed} repeats this run; {} of {read}:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
}

/// The kernel printer's round trip on a draw whose `a` in `a .. (a & (a | v)) -> b` was a
/// union of two function types, the shape of seed 76. The merge of wt/kernel9 (log
/// wt/merge-failures/20261118T193126Z-wt_kernel9-pend-step3.log, seed not recorded) met it on
/// a base without the printer fix of TYPES-meet-fns-indexed: the meet printed as
/// `(((bool -> #a) | (int ->? String)) -> bool) & (((bool -> #a) | (int ->? String) |
/// (#pair(int, int) -> f64 | String)) ->? bool)`, two arrows joined by `&`, which reads back as
/// an overload. The bounds `a` and `a & (a | v)` are one set, so the meet is the one arrow
/// `a -> bool`.
#[test]
fn a_bounded_arrow_over_a_union_of_function_types_reads_back_as_printed() {
    let pair = KType::atom_with("pair", &KType::tuple(vec![KType::int(), KType::int()]));
    let f64_or_string = &KType::f64() | &KType::string();
    let a = &KType::exact(KType::bool(), KType::atom("a"))
        | &KType::partial(KType::int(), KType::string());
    let v = &KType::exact(pair.clone(), f64_or_string.clone())
        & &KType::partial(&pair | &KType::atom("b"), f64_or_string);
    let t = &KType::exact(a.clone(), KType::bool()) & &KType::partial(&a | &v, KType::bool());
    // The text the merge's draw printed for the type built above, as `kernel_generated` writes
    // it.
    let text = "(((bool) -> (#a)) | ((int) ->? (String))) .. ((((bool) -> (#a)) | ((int) ->? \
                (String))) & ((((bool) -> (#a)) | ((int) ->? (String))) | ((#pair((int), (int))) \
                .. ((#pair((int), (int))) & ((#pair((int), (int))) | (#b))) -> ((f64) | \
                (String))))) -> (bool)";
    let printed = t.surface();
    assert!(printed.exact && printed.defs.is_empty(), "{}", printed.root);
    assert!(!printed.root.contains(" & "), "{}", printed.root);
    let mut wrong = Vec::new();
    assert!(
        !kernel_read_back(text, &printed.root, &mut wrong),
        "{}",
        printed.root
    );
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// The kernel's meet of function types, which a program cannot write with `&` alone (that is
/// an overload), prints as the one arrow it is, alone, in a union, or after a meet with an
/// atom taken away, and reads back as the type. Before the fix, each printed with `&` and read
/// back as an overload (FAIL-types-meet-exact-arrows-differing-domains, the draw
/// `((f64) | ((#a) ->? (#a))) & ((bool) ->? (rat))` of the test above).
#[test]
fn a_kernel_meet_of_function_types_prints_as_the_one_arrow_it_is() {
    let int_bool = || KType::exact(KType::int(), KType::bool());
    let pair = |a: KType, b: KType| KType::atom_with("pair", &KType::tuple(vec![a, b]));
    let cases: [(KType, &str, &str); 8] = [
        // Payloads whose first components meet in no value.
        (
            &KType::exact(
                pair(KType::string(), KType::exact(KType::int(), KType::rat())),
                KType::atom("a"),
            ) & &KType::partial(
                pair(KType::tuple(vec![]), KType::atom("a")),
                KType::atom("a"),
            ),
            "Never",
            "Never",
        ),
        // The meet as a whole (`Printer::folded`). (The draw itself is the empty function
        // alone, `Never -> Never`, which the reader does not read as the kernel does; such
        // types are not drawn, see `kernel_generated`.)
        (
            &(&KType::f64()
                | &KType::partial(
                    &KType::atom("a") | &KType::bool(),
                    &KType::atom("a") | &KType::rat(),
                ))
                & &KType::partial(KType::bool(), KType::rat()),
            "((f64) | (((#a) | (bool)) ->? ((#a) | (rat)))) & ((bool) ->? (rat))",
            "bool ->? rat",
        ),
        // A list of one block of value `false`.
        (
            &KType::exact(KType::string(), KType::int())
                & &KType::partial(KType::top(), KType::int()),
            "(String) .. ((String) & (_)) -> (int)",
            "String -> int",
        ),
        // In a union: a block of value `false`, then the one atom after it.
        (
            &(&(&KType::exact(KType::string(), KType::int())
                & &KType::partial(KType::top(), KType::int()))
                | &KType::partial(KType::f64(), KType::atom("b")))
                | &KType::atom_with("box", &KType::tuple(vec![KType::string()])),
            "(((String) .. ((String) & (_)) -> (int)) | ((f64) ->? (#b))) | (#box((String)))",
            "(f64 ->? #b) | (String -> int) | #box(String)",
        ),
        // A lower bound outside the upper: no domain lies between them, so the meet is empty.
        (
            &int_bool() & &KType::partial(KType::f64(), KType::bool()),
            "Never",
            "Never",
        ),
        // A permission wider than the other side's guarantee: the meet is that arrow.
        (
            &int_bool() & &KType::partial(&KType::int() | &KType::rat(), KType::bool()),
            "(int) -> (bool)",
            "int -> bool",
        ),
        // Two partial arrows of disjoint permissions: the meet is the one function of empty
        // domain, written `->?`, the form the checker reads as the kernel's type; it finds
        // `Never -> v` narrower (ZED_TEST_SEED=33, FAIL-types-exact-never-domain).
        (
            &KType::partial(
                KType::tuple(vec![KType::tuple(vec![]), KType::rat(), KType::string()]),
                KType::tuple(vec![KType::rat(), KType::f64()]),
            ) & &(&KType::atom("a") | &KType::partial(KType::rat(), KType::top())),
            "((((()), (rat), (String))) ->? (((rat), (f64)))) & ((#a) | ((rat) ->? (_)))",
            "Never ->? (rat, f64)",
        ),
        // An exact arrow over a union of two function types met with a partial arrow whose
        // permission is that union and more: the upper bound `a & (a | v)` is a node of its
        // own, named by no literal, but holds the same functions as the lower bound `a`, so the
        // meet is `a -> rat` (ZED_TEST_SEED=76 of the random test above, which printed the
        // meet with `&`, an overload).
        (
            {
                let a = &KType::partial(KType::rat(), KType::top())
                    | &KType::partial(KType::atom("a"), KType::top());
                let inner = &KType::exact(KType::atom("a"), KType::bool())
                    & &KType::partial(&KType::atom("a") | &KType::bool(), KType::bool());
                let v = &KType::rat() | &inner;
                &KType::exact(a.clone(), KType::rat()) & &KType::partial(&a | &v, KType::rat())
            },
            "(((rat) ->? (_)) | ((#a) ->? (_))) .. ((((rat) ->? (_)) | ((#a) ->? (_))) & \
             ((((rat) ->? (_)) | ((#a) ->? (_))) | ((rat) | ((#a) .. ((#a) & ((#a) | (bool))) \
             -> (bool))))) -> (rat)",
            "((#a ->? _) | (rat ->? _)) -> rat",
        ),
    ];
    let mut wrong = Vec::new();
    for (t, text, want) in cases {
        let printed = t.surface();
        assert_eq!(printed.root, want, "`{text}`");
        assert!(printed.exact && printed.defs.is_empty(), "`{text}`");
        assert!(
            !kernel_read_back(text, &printed.root, &mut wrong),
            "`{text}`"
        );
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// A meet of morphism literals whose built permission no literal names, `int` here, is still
/// written as the one arrow it is (`Printer::meet_text`): a type whose parts hold no other type
/// can close no cycle of the texts. Before, the meet kept its `&`, `((int | #a) ->? bool) &
/// ((int | #b) ->? bool)`, which reads with permission `int | #a | #b`, another type (row
/// FAIL-print-meet-unnamed-bound, found by ty-meet 2026-11-16).
#[test]
fn a_kernel_meet_whose_permission_no_literal_names_prints_as_one_arrow() {
    let t = &KType::partial(&KType::int() | &KType::atom("a"), KType::bool())
        & &KType::partial(&KType::int() | &KType::atom("b"), KType::bool());
    let printed = t.surface();
    assert_eq!(printed.root, "int ->? bool");
    let mut wrong = Vec::new();
    assert!(!kernel_read_back("int ->? bool", &printed.root, &mut wrong));
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// A function giving a type built to print a form.
type BuiltType = fn() -> Built;

/// The forms the kernel printer must write in
/// [`the_kernel_printer_reads_back_and_holds_no_parentheses_the_grammar_does_not_need`], each
/// with a type built to print it (checked alone by
/// [`each_kernel_type_built_for_a_form_prints_it`]): a form its draws did not print is
/// printed by its type, and no number of draws is relied on (PROOF-test-coverage-constructive).
const KERNEL_FORMS: [(&str, BuiltType); 7] = [
    (" -> ", || Built {
        t: KType::exact(KType::int(), KType::bool()),
        text: "(int) -> (bool)".into(),
    }),
    (" ->? ", || Built {
        t: KType::partial(KType::int(), KType::bool()),
        text: "(int) ->? (bool)".into(),
    }),
    (" .. ", || Built {
        t: KType::morphism(KType::int(), &KType::int() | &KType::bool(), KType::f64()),
        text: "(int) .. ((int) | (bool)) -> (f64)".into(),
    }),
    (" | ", || Built {
        t: &KType::int() | &KType::atom("a"),
        text: "(int) | (#a)".into(),
    }),
    // A meet with a union of function types: `&` of two function types alone is an overload to
    // a program, and the kernel's meet of two is printed as the one arrow it is.
    (" & ", || Built {
        t: &(&KType::exact(KType::int(), KType::bool())
            | &KType::exact(KType::f64(), KType::bool()))
            & &KType::partial(KType::top(), KType::bool()),
        text: "(((int) -> (bool)) | ((f64) -> (bool))) & ((_) ->? (bool))".into(),
    }),
    ("#box(", || Built {
        t: KType::atom_with("box", &KType::tuple(vec![KType::int()])),
        text: "#box((int))".into(),
    }),
    (",)", || Built {
        t: KType::tuple(vec![KType::int()]),
        text: "((int),)".into(),
    }),
];

/// Checks the kernel printer's text `printed` of the type built from `text`: it reads back as
/// that type, and no grouping pair of its parentheses can go. Each failure is pushed to
/// `wrong`. Gives whether the comparison was refused for unpaired functions instead.
fn kernel_read_back(text: &str, printed: &str, wrong: &mut Vec<String>) -> bool {
    let want = match parse_type(text) {
        Ok(want) => want,
        Err(e) => {
            wrong.push(format!("the reference `{text}` does not parse: {e}"));
            return false;
        }
    };
    // Two or more functions of each side at one place, each unlike those of the other side
    // there, are not paired, and the comparison is refused (COMPLEXITY.md F124): as with
    // `(rat .. (rat | _) -> f64) | (_ .. (_ | int) -> bool)` in a tuple, printed
    // `(_ -> bool) | (rat .. _ -> f64)`. A refusal is no misprint; such texts are counted.
    let refused = |x: &Ty, y: &Ty| {
        x.subtype(y)
            || x.refused(y)
                .contains("does not try every way of pairing them")
    };
    if let Ok(back) = parse_type(printed)
        && !(back.subtype(&want) && want.subtype(&back))
        && refused(&back, &want)
        && refused(&want, &back)
    {
        return true;
    }
    for w in misprinted(printed, &want) {
        wrong.push(format!("`{text}`: {w}"));
    }
    false
}

/// Each type of [`KERNEL_FORMS`] prints its form and reads back.
#[test]
fn each_kernel_type_built_for_a_form_prints_it() {
    let mut wrong = Vec::new();
    for (form, build) in KERNEL_FORMS {
        let Built { t, text } = build();
        let printed = t.surface();
        assert!(
            printed.exact && printed.defs.is_empty() && printed.root.contains(form),
            "`{text}` prints `{}`, no `{form}`",
            printed.root
        );
        assert!(
            !kernel_read_back(&text, &printed.root, &mut wrong),
            "`{text}`"
        );
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// The kernel printer's round trip on a seed whose type met a union of a payload and a partial
/// arrow with a partial arrow of disjoint key (FAIL-kernel-print-seed-15344750447356307552).
/// The text is a meet, not an overload, since one operand of `&` is a union (DESIGN.md,
/// Relation to semantic subtyping, rule (2)); a function of both has its domain within `rat`
/// and within `#pair(int, _)`, so the meet is the function of empty domain the kernel prints.
/// Before the fix the checker left `rat ->? f64` unmet, the key `#pair(int, _)` holding the
/// unknown, and read `(rat ->? f64) & (Never ->? #pair(_, #a))`.
#[test]
fn a_meet_of_partial_arrows_with_disjoint_keys_reads_back_as_printed() {
    // The text the seed drew and the kernel printer's print of the type built with it, as the
    // random test compares them; the seed reproduces the draw itself:
    // ZED_TEST_SEED=15344750447356307552 on the random test above.
    let text = "((#box((#b))) | ((rat) ->? (f64))) & ((#pair((int), (_))) ->? (#pair((_), (#a))))";
    let mut wrong = Vec::new();
    kernel_read_back(text, "Never ->? Never", &mut wrong);
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// The kernel printer's round trip on two seeds whose type met a partial arrow with an exact
/// arrow over the same keys (FAIL-kernel-print-seed-12530893063770583521). `#pair(f64, int)`
/// meets the arrow on the other side in `Never`, so the meet is that of `_ ->? #b` with an
/// exact arrow whose result holds the unknown: at a key the exact arrow guarantees, a function
/// of both answers within `#b`, since a partial arrow's answers are its values (author P350).
/// The checker took the lookup `#b | #notFound` for the values, and read the text as an arrow
/// that may answer `#notFound` (FAIL-types-partial-arrow-value-type).
#[test]
fn a_meet_of_a_partial_arrow_from_the_unknown_with_a_total_arrow_reads_back_as_printed() {
    // The texts the seeds drew and the kernel printer's prints of the types built with them, as
    // the random test compares them; each seed reproduces its draw:
    // ZED_TEST_SEED=12530893063770583521 and 7893849212256693212 on the random test above.
    let seeds = [
        (
            "((#pair((f64), (int))) | ((_) ->? (#b))) & (((int) | (#a)) .. (((int) | (#a)) | (f64)) -> ((#b) | (_)))",
            "(int | #a) .. (int | f64 | #a) -> #b",
        ),
        (
            "(((f64) -> (_)) | (String)) & ((_) ->? (((bool), (String), (rat))))",
            "f64 -> (bool, String, rat)",
        ),
    ];
    let mut wrong = Vec::new();
    for (text, printed) in seeds {
        kernel_read_back(text, printed, &mut wrong);
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// Corner cases of the fix above: the unknown on either side of the meet, a key it narrows
/// rather than empties, and keys the narrowing must leave whole. Each text reads as the type
/// written beside it (subtyping both ways).
#[test]
fn a_meet_of_partial_arrows_narrows_keys_holding_the_unknown() {
    let cases = [
        // The seed's text mirrored: the key holding the unknown is on the union's side.
        (
            "(#box(#b) | (#pair(int, _) ->? #pair(_, #a))) & (rat ->? f64)",
            "Never ->? Never",
        ),
        // Keys that meet: the arrow keeps the values of `#pair(int, int)` alone.
        (
            "(#box(#b) | (#pair(int, int) ->? #a)) & (#pair(_, int) ->? #a)",
            "#pair(int, int) ->? #a",
        ),
        // The unknown as the whole key permits every value: `rat ->? f64` stays.
        ("(#box(#b) | (rat ->? f64)) & (_ ->? f64)", "rat ->? f64"),
    ];
    for (text, want) in cases {
        let (got, want_t) = (parse_type(text).unwrap(), parse_type(want).unwrap());
        assert!(
            got.subtype(&want_t) && want_t.subtype(&got),
            "`{text}` reads `{got}`, not `{want}`"
        );
    }
}

/// The narrowing of a key by the meet of partial arrows, case by case of the proof at
/// `Domains::plain` (PROOF-domains-plain-meet): the unknown in a payload, at any depth, on
/// either side and on both; several shapes of one atom; payloads of different item counts or
/// field names, which share no value; and a key holding a function beside its payloads, met
/// exactly through the kernel. Each text reads as the type written beside it (subtyping both
/// ways): the narrowing drops no value of the meet and adds none.
#[test]
fn a_meet_of_partial_arrows_narrows_payloads_holding_the_unknown_exactly() {
    let cases = [
        (
            "(#box(#b) | (#pair(int, bool) ->? int | #a)) & (#pair(_, bool) ->? int | #c)",
            "#pair(int, bool) ->? int",
        ),
        (
            "(#box(#b) | (#box(#pair(int, _)) ->? int | #a)) & (#box(#pair(_, bool)) ->? int | #c)",
            "#box(#pair(int, bool)) ->? int",
        ),
        (
            "(#box(#b) | (#box(#pair(int, _)) ->? int)) & (#box(#pair(int, _)) ->? int)",
            "#box(#pair(int, _)) ->? int",
        ),
        (
            "(#box(#b) | (#t((int, _)) ->? int)) & ((#t((_, bool)) | #t((bool, bool))) ->? int)",
            "#t((int, bool)) ->? int",
        ),
        (
            "(#box(#b) | (#box(#box(_)) ->? int)) & ((#box(#box(int)) | #c) ->? int)",
            "#box(#box(int)) ->? int",
        ),
        (
            "(#box(#b) | ((#pair(int, _) | #q(_)) ->? int)) & ((#pair(_, bool) | #q(bool)) ->? int)",
            "(#pair(int, bool) | #q(bool)) ->? int",
        ),
        (
            "(#box(#b) | ((#pair(int, _) | #pair(_, int)) ->? int)) & (#pair(bool, _) ->? int)",
            "#pair(bool, int) ->? int",
        ),
        (
            "(#box(#b) | (#pair(#pair(int, _), _) ->? int)) & (#pair(#pair(_, bool), _) ->? int)",
            "#pair(#pair(int, bool), _) ->? int",
        ),
        (
            "(#box(#b) | (#pair(_, _) ->? int)) & ((#pair(int, _) | #pair(_, bool)) ->? int)",
            "(#pair(int, _) | #pair(_, bool)) ->? int",
        ),
        (
            "(#box(#b) | (#q(x: int) ->? int)) & (#q(_) ->? int)",
            "Never ->? int",
        ),
        (
            "(#box(#b) | (#q(x: _) ->? int)) & (#q(x: int, y: bool) ->? int)",
            "Never ->? int",
        ),
        (
            "(#box(#b) | (#q(x: _, y: bool) ->? int)) & (#q(x: int, y: _) ->? int)",
            "#q(x: int, y: bool) ->? int",
        ),
        (
            "(#box(#b) | ((#pair(int, _) | (int -> int)) ->? int)) & (#pair(int, bool) ->? int)",
            "#pair(int, bool) ->? int",
        ),
        (
            "(#box(#b) | (#box(#pair(_, #pair(_, _))) ->? int)) & (#box(#pair(int, #pair(bool, _))) ->? int)",
            "#box(#pair(int, #pair(bool, _))) ->? int",
        ),
    ];
    let mut bad = Vec::new();
    for (text, want) in cases {
        let (got, want_t) = (parse_type(text).unwrap(), parse_type(want).unwrap());
        let (a, b) = (got.subtype(&want_t), want_t.subtype(&got));
        if !(a && b) {
            bad.push(format!(
                "`{text}` reads `{got}`, not `{want}`: within it {a}, holding it {b}"
            ));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// Keys the narrowing must leave whole, since their meet with the other key could leave them
/// (PROOF-domains-plain-meet): a key whose set holds a tuple, here `(int, int)` left by
/// `(int | bool, int) & ((..) \ (bool, int))`, met with `#t((_, bool))`, whose row has no
/// kernel type and so is kept whole. Narrowed, the first arrow read `#t((_, bool)) ->? #a` and
/// bounded the values at `#t((bool, bool))`, which the function `{#t((true, true)) -> 1}`, of
/// both sides, gives as `1`: the meet lost it. The first text must read as the arrows of both
/// sides with that key left as it is, written beside it. The checker cannot show the plainer
/// claim, that the meet `#t((bool, bool)) ->? int` lies within it: it does not find the keys
/// `#t((int, int))` and `#t((bool, bool))` disjoint for a partial arrow
/// (FAIL-types-partial-arrow-same-atom-keys). The other two are checked one way, that they
/// hold the meet written beside them: a key that holds a function is left whole too, and the
/// type then reads wider than the meet.
#[test]
fn a_meet_of_partial_arrows_keeps_a_key_whose_set_holds_tuples_whole() {
    let text = "(#box(#b) | ((#t((int | bool, int) & ((..) \\ (bool, int))) ->? #a) & (#t((bool, \
                bool)) ->? int))) & (#t((_, bool)) ->? (int | #a))";
    let whole = "(#t((int | bool, int) \\ (bool, int)) ->? #a) & (#t((bool, bool)) ->? int) & \
                 ((#t((_, bool)) | #t((bool, bool))) ->? int | #a)";
    let (got, want) = (parse_type(text).unwrap(), parse_type(whole).unwrap());
    assert!(
        got.subtype(&want) && want.subtype(&got),
        "`{text}` reads `{got}`, not `{whole}`"
    );
    let cases = [
        (
            "(#box(#b) | (#t((int | bool, int) & ((..) \\ (bool, int))) ->? #a)) & (#t((_, bool)) ->? (int | #a))",
            "Never ->? Never",
        ),
        (
            "(#box(#b) | (#pair(int, _) ->? int)) & ((#pair(_, bool) | (_ -> int)) ->? int)",
            "#pair(int, bool) ->? int",
        ),
    ];
    let mut bad = Vec::new();
    for (text, want) in cases {
        let (got, want_t) = (parse_type(text).unwrap(), parse_type(want).unwrap());
        if !want_t.subtype(&got) {
            bad.push(format!(
                "`{text}` reads `{got}`, which lacks values of `{want}`"
            ));
        }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
}

/// A body expression of a recursive group built at random, `depth` levels deep at most, from
/// one-token leaves and the definition `U` itself, with the text it is built from, each
/// operand in parentheses and `U` written `#u`. Left out for the reader's sake, as in
/// [`kernel_generated`]: a complement, `_`, and a difference from a type that may hold a
/// function. Meets of any two types are built, as they are since row
/// FAIL-types-meet-function-union was fixed.
fn body_generated(rng: &mut Rng, depth: usize) -> (Expr, String) {
    if depth == 0 || rng.below(4) == 0 {
        let (e, text) = [
            (Expr::Type(KType::int()), "int"),
            (Expr::Type(KType::bool()), "bool"),
            (Expr::Type(KType::string()), "String"),
            (Expr::Type(KType::rat()), "rat"),
            (Expr::Type(KType::atom("a")), "#a"),
            (Expr::Type(KType::tuple(vec![])), "()"),
            (Expr::Ref(0, vec![]), "#u"),
            (Expr::Ref(0, vec![]), "#u"),
        ]
        .into_iter()
        .nth(rng.below(8))
        .expect("a leaf");
        return (e, text.to_string());
    }
    let mut sub = || {
        let (e, text) = body_generated(rng, depth - 1);
        (e, format!("({text})"))
    };
    let ((a, at), (b, bt), (v, vt)) = (sub(), sub(), sub());
    match rng.below(10) {
        0 => (Expr::Union(vec![a, b]), format!("{at} | {bt}")),
        1 => (Expr::And(vec![a, b]), format!("{at} & {bt}")),
        2 => (
            Expr::Diff(Box::new(Expr::Type(KType::rat())), Box::new(b)),
            format!("rat \\ {bt}"),
        ),
        3 => (Expr::Tuple(vec![a, b]), format!("({at}, {bt})")),
        4 => (Expr::Tuple(vec![a]), format!("({at},)")),
        5 => (Expr::Atom("box".into(), vec![a]), format!("#box({at})")),
        6 => (Expr::exact(a, b), format!("{at} -> {bt}")),
        7 => (
            Expr::Morphism(
                Box::new(Expr::Type(KType::empty())),
                Box::new(a),
                Box::new(b),
            ),
            format!("{at} ->? {bt}"),
        ),
        8 => (
            Expr::And(vec![
                Expr::exact(a, b.clone()),
                Expr::Morphism(
                    Box::new(Expr::Type(KType::empty())),
                    Box::new(v),
                    Box::new(b),
                ),
            ]),
            format!("({at} -> {bt}) & ({vt} ->? {bt})"),
        ),
        // A bound pair `L .. U` with `L` within `U`.
        _ => (
            Expr::Morphism(
                Box::new(a.clone()),
                Box::new(Expr::Union(vec![a, b])),
                Box::new(v),
            ),
            format!("{at} .. ({at} | {bt}) -> {vt}"),
        ),
    }
}

/// The text the recursive-group printer `Show` (crates/zed-kernel/src/types/rec/unfold.rs)
/// writes for `e`, read from the message that rejects `type U = !(e)` when `e` names `U`, with
/// `U` written `#u`; none when the group is rejected for another reason first or is admitted.
fn shown(e: Expr) -> Option<String> {
    let def = Def {
        name: "U".into(),
        params: Vec::new(),
        body: Expr::Not(Box::new(e)),
    };
    let message = Group::new(vec![def]).err()?.message;
    let (_, rest) = message.split_once("which is not monotone in `")?;
    let (text, _) = rest.split_once("`: a larger")?;
    let words = text.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '#'));
    words
        .clone()
        .all(|w| w == "U" || !w.starts_with(char::is_uppercase) || w == "String" || w == "Never")
        .then(|| {
            let mut out = String::new();
            let mut last = 0;
            for (i, _) in text.match_indices('U') {
                let alone = |c: Option<char>| !c.is_some_and(|c| c.is_alphanumeric() || c == '_');
                if alone(text[..i].chars().next_back()) && alone(text[i + 1..].chars().next()) {
                    out += &text[last..i];
                    out += "#u";
                    last = i + 1;
                }
            }
            out + &text[last..]
        })
}

/// The recursive-group printer `Show` over body expressions built at random: each text it
/// writes reads back as the expression it was built from (round trip), and no grouping pair of
/// its parentheses can go (minimality). Author rule P191; row FAIL-print-kernel-parens, where
/// `Show` wrote every key of `->` in a pair, `(U) -> U`. Negative control: the hand cases at the
/// top, one key in a pair the grammar does not need, are caught.
#[test]
fn the_group_printer_reads_back_and_holds_no_parentheses_the_grammar_does_not_need() {
    let u = || Expr::Ref(0, vec![]);
    let key = shown(Expr::exact(u(), u())).expect("a complement message");
    assert_eq!(key, "#u -> #u");
    let want = parse_type("#u -> #u").unwrap();
    assert_eq!(
        misprinted("(#u) -> #u", &want),
        ["`(#u) -> #u`: `#u -> #u` parses the same"]
    );
    let mut rng = Rng::new(zed_tests::seed::seed(
        "the_group_printer_reads_back_and_holds_no_parentheses_the_grammar_does_not_need",
    ));
    let (mut wrong, mut read, mut seen) = (Vec::new(), 0, HashSet::new());
    let mut forms = GROUP_FORMS.map(|(f, _)| (f, 0usize));
    for _ in 0..3000 {
        let (e, text) = body_generated(&mut rng, 3);
        let Some(printed) = shown(e) else { continue };
        if !seen.insert(printed.clone()) {
            continue;
        }
        read += 1;
        for (f, n) in forms.iter_mut() {
            *n += usize::from(printed.contains(*f));
        }
        group_read_back(&text, &printed, &mut wrong);
    }
    eprintln!("{read} distinct texts read: {forms:?}");
    // A form the draws did not print is printed by the body built for it, checked as the
    // draws are.
    for ((form, n), (_, build)) in forms.iter().zip(GROUP_FORMS) {
        if *n > 0 {
            continue;
        }
        let (e, text) = build();
        let printed = shown(e).unwrap_or_else(|| panic!("`{text}` is not shown"));
        assert!(
            printed.contains(form),
            "`{form}` is not printed: `{text}` prints `{printed}`"
        );
        group_read_back(&text, &printed, &mut wrong);
        eprintln!("`{form}` printed only by `{text}`");
    }
    assert!(
        wrong.is_empty(),
        "{} of {read}:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
}

/// A function giving a group body and the text it prints.
type GroupBody = fn() -> (Expr, String);

/// The forms the group printer must write in
/// [`the_group_printer_reads_back_and_holds_no_parentheses_the_grammar_does_not_need`], each
/// with a body built to print it (checked alone by
/// [`each_group_body_built_for_a_form_prints_it`]): a form its draws did not print is printed
/// by its body, and no number of draws is relied on (PROOF-test-coverage-constructive).
const GROUP_FORMS: [(&str, GroupBody); 8] = [
    (" -> ", || {
        (
            Expr::exact(Expr::Ref(0, vec![]), Expr::Type(KType::int())),
            "(#u) -> (int)".into(),
        )
    }),
    (" ->? ", || {
        (
            group_partial(Expr::Ref(0, vec![]), Expr::Type(KType::int())),
            "(#u) ->? (int)".into(),
        )
    }),
    (" .. ", || {
        let int = || Expr::Type(KType::int());
        let upper = Expr::Union(vec![int(), Expr::Ref(0, vec![])]);
        let e = Expr::Morphism(
            Box::new(int()),
            Box::new(upper),
            Box::new(Expr::Ref(0, vec![])),
        );
        (e, "(int) .. ((int) | (#u)) -> (#u)".into())
    }),
    // A recursive occurrence needs a tuple, payload or function type above it.
    (" | ", || {
        let e = Expr::Union(vec![
            Expr::Tuple(vec![Expr::Ref(0, vec![])]),
            Expr::Type(KType::int()),
        ]);
        (e, "((#u),) | (int)".into())
    }),
    (" & ", || {
        let e = Expr::And(vec![
            Expr::exact(Expr::Ref(0, vec![]), Expr::Type(KType::int())),
            group_partial(Expr::Type(KType::bool()), Expr::Type(KType::int())),
        ]);
        (e, "((#u) -> (int)) & ((bool) ->? (int))".into())
    }),
    (" \\ ", || {
        let e = Expr::Diff(
            Box::new(Expr::Type(KType::rat())),
            Box::new(Expr::Ref(0, vec![])),
        );
        (
            Expr::Atom("box".into(), vec![e]),
            "#box((rat \\ (#u)))".into(),
        )
    }),
    ("#box(", || {
        (
            Expr::Atom("box".into(), vec![Expr::Ref(0, vec![])]),
            "#box((#u))".into(),
        )
    }),
    (",)", || {
        (Expr::Tuple(vec![Expr::Ref(0, vec![])]), "((#u),)".into())
    }),
];

/// The body `k ->? v`, as [`body_generated`] builds it.
fn group_partial(k: Expr, v: Expr) -> Expr {
    Expr::Morphism(
        Box::new(Expr::Type(KType::empty())),
        Box::new(k),
        Box::new(v),
    )
}

/// Checks the group printer's text `printed` of the body built from `text`: it reads back as
/// that body, and no grouping pair of its parentheses can go. Each failure is pushed to
/// `wrong`.
fn group_read_back(text: &str, printed: &str, wrong: &mut Vec<String>) {
    match parse_type(text) {
        Ok(want) => {
            for w in misprinted(printed, &want) {
                wrong.push(format!("`{text}`: {w}"));
            }
        }
        Err(e) => wrong.push(format!("the reference `{text}` does not parse: {e}")),
    }
}

/// Each body of [`GROUP_FORMS`] is shown with its form and reads back.
#[test]
fn each_group_body_built_for_a_form_prints_it() {
    let mut wrong = Vec::new();
    for (form, build) in GROUP_FORMS {
        let (e, text) = build();
        let printed = shown(e).unwrap_or_else(|| panic!("`{text}` is not shown"));
        assert!(
            printed.contains(form),
            "`{text}` prints `{printed}`, no `{form}`"
        );
        group_read_back(&text, &printed, &mut wrong);
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// A partial arrow first in a group message, `U ->? ()`, is written without its guarantee,
/// which is `Never`. `Show` used to print that guarantee and then drop its text, and with it the
/// mark the message's naming pass reads as the start of the printed types, so naming the
/// message's parts panicked ("a type is opened before it is closed"). Found by the test below.
#[test]
fn a_group_message_opening_with_a_partial_arrow_is_written() {
    let partial = |k: Expr, v: Expr| {
        Expr::Morphism(
            Box::new(Expr::Type(KType::empty())),
            Box::new(k),
            Box::new(v),
        )
    };
    let u = || Expr::Ref(0, vec![]);
    let (unit, int) = (
        || Expr::Type(KType::tuple(vec![])),
        || Expr::Type(KType::int()),
    );
    assert_eq!(shown(partial(u(), unit())).as_deref(), Some("#u ->? ()"));
    assert_eq!(
        shown(Expr::Atom("box".into(), vec![partial(int(), u())])).as_deref(),
        Some("#box(int ->? #u)")
    );
    // Negative control: the arrow later in the text was written before the repair too.
    assert_eq!(
        shown(Expr::Tuple(vec![unit(), partial(int(), u())])).as_deref(),
        Some("((), int ->? #u)")
    );
}

/// A tuple key written by a name needs no parentheses: `Part1 -> (Part1,)`, not
/// `(Part1) -> (Part1,)`. The printer used to put the pair a tuple key needs, `((A, B)) -> V`,
/// around the reference to the tuple before the naming pass decided whether to name it, so a named
/// key kept the pair. Found by
/// `printed_types_read_back_and_hold_no_parentheses_the_grammar_does_not_need`, whose case depends
/// on what other tests have printed in the process.
#[test]
fn a_tuple_key_written_by_a_name_has_no_parentheses() {
    for (text, want) in [
        (
            "(((), rat)) -> (((), rat),)",
            "type Part1 = ((), rat);\nPart1 -> (Part1,)",
        ),
        // Negative controls: written in full, the key keeps the pair it needs.
        ("(((), rat)) -> ((), rat)", "(((), rat)) -> ((), rat)"),
        ("((int, int)) -> int", "((int, int)) -> int"),
    ] {
        assert_eq!(parse_type(text).unwrap().to_string(), want, "{text}");
    }
}

/// An intersection of functions with one parameter list is read as one function holding
/// each operand's arrows: the checker moves the first operand's function out of its type and
/// adds the others' arrows to it (`and` in zedc-check). The function's hash is read as soon
/// as it is put in a type, so the function moved out must drop the hash it kept
/// (`Sig::unwrap_to_change`); before, it kept the hash of its first arrow alone, and the
/// tuple holding it was unequal to, and no subtype of, the same tuple read from its print
/// (seed 16437813929499442776 of the round-trip test above), though the intersection alone
/// compared equal, its hash read only after the arrows were joined.
#[test]
fn an_intersection_of_functions_in_a_tuple_equals_its_print_read_back() {
    for text in [
        "(((bool ->? String) .. ((bool ->? String) | (rat,)) -> int \\ 0),)",
        "(((bool ->? String) -> int \\ 0) & (((rat,) | (bool ->? String)) -> (int \\ 0) | #notFound),)",
        "((int -> int) & (bool -> bool), int)",
        "#a((int -> int) & (bool -> bool) & (rat -> rat))",
    ] {
        let t = parse_type(text).unwrap();
        let back = parse_type(&t.to_string()).unwrap();
        assert!(t == back, "{text}: {t} and {back}");
        assert!(
            t.subtype(&back) && back.subtype(&t),
            "{text}: {t} and {back}"
        );
    }
}

/// The kernel printer's round trip on a seed whose type bounds a domain by the meet of a
/// function type of two domain bounds with a union holding another
/// (FAIL-kernel-print-seed-4238766106498969688). With `X = f64 .. (f64 | #a) -> ()` and `Y = f64
/// .. (f64 | ()) -> ()`, the upper bound is `A & (A | B)` for `A = X .. (X & (X | f64)) -> _`
/// and `B` an arrow over `Y`; the kernel's `A` is `X -> _`, and so is the bound, which the
/// printer writes without the parentheses `-> String ->? int` needs none of. The print was
/// right; the checker kept `(X -> _) & (Y .. .. -> ((), ()))` as both arrows, within neither
/// side, where a function of `X` (of domain `f64 | #a`) is outside `Y`'s permission, so that
/// meet is empty, and read the text as another type.
#[test]
fn a_bound_meeting_function_types_of_two_domain_bounds_reads_back_as_printed() {
    // The text the seed drew and the kernel printer's print of the type built with it, as the
    // random test compares them; the seed reproduces the draw itself:
    // ZED_TEST_SEED=4238766106498969688 on the random test above.
    let text = "(((f64) .. ((f64) | (#a)) -> (())) .. (((f64) .. ((f64) | (#a)) -> (())) & (((f64) .. ((f64) | (#a)) -> (())) | (f64))) -> (_)) .. ((((f64) .. ((f64) | (#a)) -> (())) .. (((f64) .. ((f64) | (#a)) -> (())) & (((f64) .. ((f64) | (#a)) -> (())) | (f64))) -> (_)) & ((((f64) .. ((f64) | (#a)) -> (())) .. (((f64) .. ((f64) | (#a)) -> (())) & (((f64) .. ((f64) | (#a)) -> (())) | (f64))) -> (_)) | (((f64) .. ((f64) | (())) -> (())) .. (((f64) .. ((f64) | (())) -> (())) | ((f64) | (_))) -> (((()), (())))))) -> ((String) ->? (int))";
    let mut wrong = Vec::new();
    kernel_read_back(
        text,
        "((f64 .. (f64 | #a) -> ()) -> _) -> String ->? int",
        &mut wrong,
    );
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}

/// The kernel printer's round trip on the draw of seed 8999424735008423254
/// (FAIL-kernel-print-seed-8999424735008423254): the meet of `_ ->? ()` and
/// `rat .. (rat & (rat | int)) -> rat`, beside `String` on both sides. A function of both
/// takes every `rat` and gives a value of `rat & ()`, which holds none, so the meet holds no
/// function (DESIGN.md sec:type_language, "Relation to semantic subtyping", point (1): "`t ->
/// V` is empty here when `t` is inhabited and `V` is empty"), and the type is `String`. Before
/// the fix the kernel printed the meet as `rat -> Never`, `String | (rat -> Never)`, which the
/// checker reads as holding a function, so the text read back as another type. Control: the
/// kernel holds the type built here within `String`, so the printer, not the kernel's meet,
/// was wrong.
#[test]
fn a_meet_of_arrows_whose_values_share_none_prints_as_no_function() {
    let left = &KType::partial(KType::top(), KType::tuple(vec![])) | &KType::string();
    let rat_int = &KType::rat() | &KType::int();
    let right = &(&KType::exact(KType::rat(), KType::rat())
        & &KType::partial(rat_int, KType::rat()))
        | &KType::string();
    let t = &left & &right;
    assert!((&t - &KType::string()).is_empty());
    // The text the seed drew for the type built above, as `kernel_generated` writes it; the
    // seed reproduces the draw itself: ZED_TEST_SEED=8999424735008423254 on the random test
    // above.
    let text =
        "(((_) ->? (())) | (String)) & (((rat) .. ((rat) & ((rat) | (int))) -> (rat)) | (String))";
    let printed = t.surface();
    assert!(printed.exact && printed.defs.is_empty(), "{}", printed.root);
    assert!(!printed.root.contains("->"), "{}", printed.root);
    let mut wrong = Vec::new();
    assert!(
        !kernel_read_back(text, &printed.root, &mut wrong),
        "{}",
        printed.root
    );
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
