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

use zed_kernel::types::{TextPlace, Type as KType};
use zedc::check::read::parse_type;
use zedc::check::ty::Ty;
use zedc::parse::{Grammar, grammar, marked_rule};

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
/// `TypeNot`; a key (`TypeUnion '->' Arrow`) and a bound (`TypeUnion '..' TypeUnion`) are
/// `TypeUnion`s.
const PLACES: [(TextPlace, &[&str]); 7] = [
    (TextPlace::Any, &["Arrow"]),
    (TextPlace::Union, &["TypeAnd"]),
    (TextPlace::And, &["TypeNot"]),
    (TextPlace::DiffLeft, &["TypeDiff", "TypeNot"]),
    (TextPlace::Prim, &["TypeNot"]),
    (TextPlace::Key, &["TypeUnion"]),
    (TextPlace::Bound, &["TypeUnion"]),
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

/// A random number generator for [`generated`]: SplitMix64, seeded by [`zed_tests::seed::seed`].
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let x = (self.0 ^ (self.0 >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        let x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        ((x ^ (x >> 31)) % n as u64) as usize
    }
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
/// order and form, so `(bool, bool) | (1, f64)` and `(1, f64) | (bool, bool)` read apart, and
/// the reader keeps the other members of a union that holds `_`, which the printer drops,
/// since `_` absorbs them (A92). Subtyping alone does not tell payloads apart, `#box(#pair(f64,
/// bool))` from `#box(#pairf64, bool)`, so the texts must agree too.
fn same(a: &Ty, b: &Ty) -> bool {
    stated(a) == stated(b) || (a.subtype(b) && b.subtype(a) && a.to_string() == b.to_string())
}

/// Types generated at random, each printed: the text parses back to the type (round trip), and
/// deleting any one pair of its parentheses either fails to parse or gives another type
/// (minimality). The forms the printed texts hold are counted, so that a generator that stops
/// reaching one shows.
#[test]
fn printed_types_read_back_and_hold_no_parentheses_the_grammar_does_not_need() {
    let mut rng = Rng(zed_tests::seed::seed(
        "printed_types_read_back_and_hold_no_parentheses_the_grammar_does_not_need",
    ));
    let mut wrong = Vec::new();
    let mut read = 0;
    let mut seen = HashSet::new();
    let mut forms = [
        " -> ", " ->? ", " .. ", " | ", " & ", " \\ ", " for ", "#box(", ",)",
    ]
    .map(|f| (f, 0usize));
    for _ in 0..3000 {
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
        match parse_type(&printed) {
            Ok(back) if same(&back, &t) => {}
            Ok(_) => wrong.push(format!(
                "`{text}` prints `{printed}`, read back as another type"
            )),
            Err(e) => wrong.push(format!(
                "`{text}` prints `{printed}`, which does not parse: {e}"
            )),
        }
        for (a, b) in pairs(&printed) {
            let less = format!(
                "{}{}{}",
                &printed[..a],
                &printed[a + 1..b],
                &printed[b + 1..]
            );
            if parse_type(&less).is_ok_and(|back| same(&back, &t)) {
                wrong.push(format!(
                    "`{text}` prints `{printed}`; `{less}` reads the same"
                ));
            }
        }
    }
    assert!(
        wrong.is_empty(),
        "{} of {read}:\n{}",
        wrong.len(),
        wrong.join("\n")
    );
    assert!(read >= 300, "only {read} distinct types read: {forms:?}");
    assert!(
        forms.iter().all(|(_, n)| *n > 0),
        "a form never printed: {forms:?}"
    );
}

/// Hand-picked cases of the rule, each with its printed text: a function of one positional
/// parameter is written `K -> R`, its key parenthesized only where the grammar needs it.
#[test]
fn function_types_print_with_exactly_the_parentheses_the_grammar_needs() {
    let cases = [
        ("(int) -> int", "int -> int"),
        ("int -> int", "int -> int"),
        ("((int) -> int) -> int", "(int -> int) -> int"),
        ("(int) -> (int) -> int", "int -> int -> int"),
        ("((int, int)) -> int", "((int, int)) -> int"),
        ("(int, int) -> int", "(int, int) -> int"),
        ("((int,)) -> int", "(int,) -> int"),
        ("(()) -> int", "(()) -> int"),
        ("() -> int", "() -> int"),
        ("(int | #a) -> int", "int | #a -> int"),
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
        // The clause at the end bounds the members before it too, so it takes a name none of
        // their clauses wrote: `for T` twice does not read.
        (
            "((T) -> T for T in int | f64) | (((T) -> T for T in int | f64)) & ((_) ->? (String))",
            "(T -> T for T in int | f64) | (U -> U) & (_ -> String | #notFound) for U in int | f64",
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
