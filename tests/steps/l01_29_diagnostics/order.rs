//! Item order (step L1.29b; the `Unit` row of the kernel desugaring table, DESIGN.md
//! sec:grammar). A unit is the environment of its items' bindings, not a sequence: the checker
//! visits vertices by name and then content address, and evaluation follows dependency edges.
//! So moving a unit's items, each with its annotations and comments, while the declarations of
//! each name keep their written order, changes no verdict, diagnostic or test outcome other
//! than in its position. Each corpus and step unit is checked as written, with its items
//! reversed, and in one seeded shuffle, and every answer is keyed by the item it lies in and its
//! offset within that item.

use std::collections::{HashMap, VecDeque};
use std::path::{Path, PathBuf};

use zed_tests::instances::Rng;
use zed_tests::scaling;
use zedc::lex::{Tok, lex_with_docs};
use zedc::parse::{TOP, Tree, parse};
use zedc::query::Db;
use zedc::rejection::Row;
use zedc::testing::test;

/// The seed of the one shuffle each unit is checked in.
const SEED: u64 = 0x1_29b;

/// A unit's text cut into its items. Item `i` is `text[cuts[i]..cuts[i + 1]]`: its leading
/// comments, annotations and declaration, and the rest of its last line when that holds only
/// white space and a `//` comment other than a doc comment, such as a `// ✗` mark. The text
/// before the first item goes with it. The text after the last item's line, `text[cuts[len]..]`,
/// is the unit's tail, which stays at the end: a `///` block there documents no declaration
/// in any order. A doc comment at the end of an item's line documents the next item, so it is
/// cut with that one.
pub(super) struct Items<'t> {
    text: &'t str,
    pub(super) cuts: Vec<usize>,
    /// The names each item declares: each named target of a binding `a, b = …`, otherwise the
    /// first name of its declaration; none for a unit annotation.
    names: Vec<Vec<&'t str>>,
}

/// The items of `text`; one item, the whole text, when it does not lex or parse.
pub(super) fn items(text: &str) -> Items<'_> {
    let whole = Items {
        text,
        cuts: vec![0, text.len()],
        names: vec![Vec::new()],
    };
    let Ok((tokens, _)) = lex_with_docs(text) else {
        return whole;
    };
    let Ok(tree) = parse(text, &tokens, "Unit", TOP) else {
        return whole;
    };
    let kids: Vec<usize> = tree.nodes[tree.root]
        .kids
        .iter()
        .copied()
        .filter(|&k| tree.name(k) == "Item")
        .collect();
    if kids.is_empty() {
        return whole;
    }
    let mut cuts = vec![0];
    let mut names = Vec::with_capacity(kids.len());
    for &k in &kids {
        let node = &tree.nodes[k];
        cuts.push(line_rest(text, tokens[node.end - 1].span.end));
        names.push(declared(text, &tokens, &tree, k));
    }
    Items { text, cuts, names }
}

/// The end of the line from byte `at` of `text`, its line break included, when the rest of the
/// line is white space and at most a `//` comment that is not a doc comment (`///` and not
/// `////`, as the lexer reads one); otherwise `at`.
fn line_rest(text: &str, at: usize) -> usize {
    let rest = &text[at..];
    let blank = rest.trim_start_matches([' ', '\t']);
    let after = at + rest.len() - blank.len();
    let doc = blank.starts_with("///") && !blank.starts_with("////");
    if (blank.starts_with("//") && !doc) || blank.starts_with('\n') || blank.is_empty() {
        text[after..]
            .find('\n')
            .map_or(text.len(), |i| after + i + 1)
    } else {
        at
    }
}

/// The names the declaration of item node `item` declares, found in pre-order with an explicit
/// stack, outside its annotations: each named target of a binding (`PlainBinding = Target %
/// ',' '=' Expr …`, so `a, _, b = e` declares `a` and `b`), otherwise its first name token;
/// none for a unit annotation.
fn declared<'t>(
    text: &'t str,
    tokens: &[zedc::lex::Token],
    tree: &Tree,
    item: usize,
) -> Vec<&'t str> {
    let name = |n: usize| {
        let t = &tokens[tree.nodes[n].start];
        assert!(matches!(t.tok, Tok::Name(_)), "a `Name` node is a name");
        &text[t.span.start..t.span.end]
    };
    let mut stack = vec![item];
    while let Some(n) = stack.pop() {
        match tree.name(n) {
            "Annot" | "UnitAnnot" => continue,
            "Name" => return vec![name(n)],
            // A target is a `Name` or `_`; the value and boundary after the targets are not.
            "PlainBinding" => {
                return (tree.nodes[n].kids.iter())
                    .filter(|&&k| tree.name(k) == "Target")
                    .flat_map(|&k| tree.nodes[k].kids.first().map(|&m| name(m)))
                    .collect();
            }
            _ => stack.extend(tree.nodes[n].kids.iter().rev()),
        }
    }
    Vec::new()
}

impl<'t> Items<'t> {
    pub(super) fn len(&self) -> usize {
        self.names.len()
    }

    /// `order` with the items of each name put back in their written order. Items that share a
    /// name are joined, and the joins taken transitively, so `a, b = …` joins the items of `a`
    /// with those of `b`; the places the items of a join take in `order` are given to them in
    /// written order. A join may hold two items with no name in common, which then also keep
    /// their written order: a coarser restriction than each name's, and still a permutation.
    /// O(i·α(i)) for i items, by union-find with union by size and path halving, over one hash
    /// lookup per declared name.
    fn keep_names(&self, order: Vec<usize>) -> Vec<usize> {
        let n = self.len();
        let mut parent: Vec<usize> = (0..n).collect();
        let mut size = vec![1usize; n];
        let find = |parent: &mut [usize], mut i: usize| {
            while parent[i] != i {
                parent[i] = parent[parent[i]];
                i = parent[i];
            }
            i
        };
        let mut first: HashMap<&str, usize> = HashMap::new();
        for (i, names) in self.names.iter().enumerate() {
            for &name in names {
                let j = *first.entry(name).or_insert(i);
                let (a, b) = (find(&mut parent, i), find(&mut parent, j));
                if a != b {
                    let (big, small) = if size[a] >= size[b] { (a, b) } else { (b, a) };
                    parent[small] = big;
                    size[big] += size[small];
                }
            }
        }
        // The items of each join in written order, under the join's root.
        let mut written = vec![VecDeque::new(); n];
        for i in 0..n {
            written[find(&mut parent, i)].push_back(i);
        }
        order
            .into_iter()
            .map(|i| {
                written[find(&mut parent, i)]
                    .pop_front()
                    .expect("one place per item of the join")
            })
            .collect()
    }

    /// The reversed order and one seeded shuffle, each keeping each name's written order.
    pub(super) fn orders(&self) -> [Vec<usize>; 2] {
        let reversed = (0..self.len()).rev().collect();
        let mut shuffled: Vec<usize> = (0..self.len()).collect();
        let mut rng = Rng::new(SEED);
        for i in (1..shuffled.len()).rev() {
            shuffled.swap(i, rng.below(i + 1));
        }
        [self.keep_names(reversed), self.keep_names(shuffled)]
    }

    /// The text with its items in `order`, each followed by a line break when it ends without
    /// one, then the tail, and where each item and the tail (numbered `len`) start in it. The
    /// written order gives the text unchanged when its items end with line breaks.
    pub(super) fn permuted(&self, order: &[usize]) -> Permuted {
        let mut text = String::with_capacity(self.text.len() + order.len());
        let mut starts = Vec::with_capacity(order.len());
        for &i in order {
            starts.push((text.len(), i));
            text += &self.text[self.cuts[i]..self.cuts[i + 1]];
            if order.len() > 1 && !text.ends_with('\n') {
                text.push('\n');
            }
        }
        starts.push((text.len(), self.len()));
        text += &self.text[self.cuts[self.len()]..];
        Permuted { text, starts }
    }
}

/// A permuted text, and the start of each item and of the tail in it, in increasing order,
/// with the item.
pub(super) struct Permuted {
    pub(super) text: String,
    starts: Vec<(usize, usize)>,
}

/// A place in a unit: the item, by its written index, and the byte offset within that item.
type Place = (usize, usize);

/// What the checker says of a unit, each part placed by item and offset: whether it is
/// accepted; its diagnostics, or its warnings, each with its row, message and steps; and the
/// outcome of each check `zedc test` runs on it.
#[derive(PartialEq, Eq, Debug)]
struct Answer {
    accepted: bool,
    diagnostics: Vec<Said>,
    outcomes: Vec<(Place, Option<String>)>,
}

/// A diagnostic or warning, placed.
#[derive(PartialEq, Eq, PartialOrd, Ord, Debug)]
struct Said {
    at: Place,
    row: Option<Row>,
    message: String,
    /// Each step's place, text and width, in the order of the derivation.
    steps: Vec<(Place, String, usize)>,
}

impl Permuted {
    /// The place of the 1-based `line` and `col` (counted in Unicode scalars) of the text,
    /// from `lines`, the start of each line.
    fn place(&self, lines: &[usize], line: usize, col: usize) -> Place {
        let start = lines[line - 1];
        let offset = start
            + self.text[start..]
                .chars()
                .take(col - 1)
                .map(char::len_utf8)
                .sum::<usize>();
        let k = self.starts.partition_point(|&(s, _)| s <= offset) - 1;
        let (s, item) = self.starts[k];
        (item, offset - s)
    }

    /// What the checker says of the text, placed.
    fn answer(&self) -> Answer {
        let text = &self.text;
        let lines: Vec<usize> = std::iter::once(0)
            .chain(text.match_indices('\n').map(|(i, _)| i + 1))
            .collect();
        let said = |d: &zedc::front::Diagnostic| Said {
            at: self.place(&lines, d.line, d.col),
            row: d.row,
            message: d.message.clone(),
            steps: d
                .steps
                .iter()
                .map(|s| (self.place(&lines, s.line, s.col), s.text.clone(), s.width))
                .collect(),
        };
        let mut db = Db::new();
        let front = db.front(text);
        let (accepted, mut diagnostics) = match &*front {
            Ok((_, _, warnings)) => (true, warnings.iter().map(said).collect::<Vec<_>>()),
            Err(ds) => (false, ds.iter().map(said).collect()),
        };
        diagnostics.sort();
        // The outcomes of a rejected unit are its diagnostics checked against its marks, so
        // they are compared through the diagnostics.
        let mut outcomes: Vec<(Place, Option<String>)> = if accepted {
            zedc::testing::test_in(&mut db, text)
                .into_iter()
                .map(|o| (self.place(&lines, o.line, o.col), o.failure))
                .collect()
        } else {
            Vec::new()
        };
        outcomes.sort();
        Answer {
            accepted,
            diagnostics,
            outcomes,
        }
    }
}

/// `answer` with each unsatisfiable set of declared constraints whose places lie in more than
/// one item reduced to its row: which minimal set of witnesses deletion finds, and the place
/// where the last of them arrived, follow the order of the sites (DESIGN.md sec:constraints).
fn across_items_by_verdict(mut answer: Answer, name: &str) -> Answer {
    for d in &mut answer.diagnostics {
        let spans_items = d.steps.iter().any(|s| s.0.0 != d.at.0);
        if d.row == Some(Row::UnsatisfiableConstraints) && spans_items {
            // Each witness set reported must still be checked minimal, by deleting each of its
            // constraints and checking the rest are satisfiable; that needs the store of
            // declared constraints that step L10.4 builds, and no L1 diagnostic is in this row.
            panic!(
                "{name}: an unsatisfiable set of declared constraints across items; check each \
                 reported witness set minimal here (step L1.29b, with step L10.4)"
            );
        }
    }
    answer
}

/// Every `.zed` unit of the corpus, with its program folders, variants and controls, and of
/// the steps' `zed/` folders, by path.
pub(super) fn units() -> Vec<(String, String)> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut dirs = vec![root.join("../zed/corpus")];
    for step in std::fs::read_dir(root.join("steps")).unwrap() {
        dirs.push(step.unwrap().path().join("zed"));
    }
    let mut out = Vec::new();
    while let Some(dir) = dirs.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for e in entries {
            let path = e.unwrap().path();
            if path.is_dir() && !path.ends_with("ref") {
                dirs.push(path);
            } else if path.extension().is_some_and(|x| x == "zed") {
                let text = zedc::source::load(&std::fs::read(&path).unwrap())
                    .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
                out.push((shown(&root, &path), text));
            }
        }
    }
    out.sort();
    out
}

/// `path` from the test crate's parent.
fn shown(root: &Path, path: &Path) -> String {
    let parent = root.parent().unwrap();
    path.strip_prefix(parent)
        .or_else(|_| path.strip_prefix(root))
        .unwrap_or(path)
        .display()
        .to_string()
}

/// Checks `text`, the unit `name`, in each of `orders` of its items `items` against its
/// written order.
fn check_unit(name: &str, text: &str, items: &Items, orders: &[(&str, Vec<usize>)]) {
    let written = Permuted {
        text: text.to_string(),
        starts: items.cuts.iter().copied().zip(0..).collect(),
    };
    let want = across_items_by_verdict(written.answer(), name);
    for (how, order) in orders {
        let p = items.permuted(order);
        let got = across_items_by_verdict(p.answer(), name);
        assert_eq!(
            want, got,
            "{name}: the items {how}, in the order {order:?}:\n{}",
            p.text
        );
    }
}

/// Checks the units of `units` whose index is `piece` modulo `pieces`, each as written,
/// reversed and shuffled.
fn check_piece(units: &[(String, String)], piece: usize, pieces: usize) {
    for (name, text) in units.iter().skip(piece).step_by(pieces) {
        let items = items(text);
        let orders = ["reversed", "shuffled"].into_iter().zip(items.orders());
        check_unit(name, text, &items, &orders.collect::<Vec<_>>());
    }
}

/// The pieces the units are checked in, each a test of its own, so each runs in parallel and
/// within the time of one piece of the suite.
const PIECES: usize = 4;

/// The units of more than one item, which are moved, on 2026-11-03: 39 of 63. Of the other 24,
/// 23 parse and declare one item, such as a lone `main` (01, 02, 04, 05, 06, 18, 20, 21/stats,
/// 25, 26, five controls, the four variants, and config, retry, shape and narrowed of the steps),
/// so they have no other order, and `controls/neg-parse-error.zed` does not parse, by design.
/// The test fails when fewer are moved, as when a parser change stops a unit from parsing.
const MOVED: usize = 39;

fn piece(i: usize) {
    let units = units();
    assert!(units.len() >= 63, "{} units", units.len());
    let moved = units.iter().filter(|(_, t)| items(t).len() > 1).count();
    assert!(
        moved >= MOVED,
        "{moved} units of more than one item, not {MOVED}"
    );
    check_piece(&units, i, PIECES);
}

#[test]
fn moving_the_items_of_each_unit_changes_nothing_but_positions_0() {
    piece(0);
}

#[test]
fn moving_the_items_of_each_unit_changes_nothing_but_positions_1() {
    piece(1);
}

#[test]
fn moving_the_items_of_each_unit_changes_nothing_but_positions_2() {
    piece(2);
}

#[test]
fn moving_the_items_of_each_unit_changes_nothing_but_positions_3() {
    piece(3);
}

/// A small unit of three items, one rejected: what each answer is keyed by moves with its
/// item.
const ACCOUNTS: &str = "\
// The balance after the monthly fee.
fee(positional balance) = balance - 2
test { 10 -> 8, 0 -> -2 }

// A deposit's balance, from a total that nothing declares.
deposit(positional amount) = total + amount; // ✗

// A balance rounded down to a whole ten.
tens(positional balance) = balance div 10 * 10
test { 25 -> 20 }
";

#[test]
fn a_units_items_are_cut_with_their_comments_tables_and_marks() {
    let items = items(ACCOUNTS);
    assert_eq!(items.names, [["fee"], ["deposit"], ["tens"]]);
    let texts: Vec<&str> = (0..items.len())
        .map(|i| &ACCOUNTS[items.cuts[i]..items.cuts[i + 1]])
        .collect();
    assert_eq!(
        texts,
        [
            "// The balance after the monthly fee.\nfee(positional balance) = balance - 2\n\
             test { 10 -> 8, 0 -> -2 }\n",
            "\n// A deposit's balance, from a total that nothing declares.\n\
             deposit(positional amount) = total + amount; // ✗\n",
            "\n// A balance rounded down to a whole ten.\n\
             tens(positional balance) = balance div 10 * 10\ntest { 25 -> 20 }\n",
        ]
    );
}

/// Two items on one line are cut between them, and each is given a line of its own when moved.
#[test]
fn two_items_on_one_line_are_cut_apart() {
    let text = "low = 1; high = 9; // the bounds\nspan = high - low;\n";
    let items = items(text);
    assert_eq!(items.names, [["low"], ["high"], ["span"]]);
    assert_eq!(items.cuts, [0, 8, 33, text.len()]);
    let p = items.permuted(&[2, 1, 0]);
    assert_eq!(
        p.text,
        "span = high - low;\n high = 9; // the bounds\nlow = 1;\n"
    );
    assert_eq!(items.permuted(&[0, 1, 2]).answer(), p.answer());
}

#[test]
fn a_diagnostic_moves_with_its_item() {
    let items = items(ACCOUNTS);
    let order: Vec<usize> = (0..items.len()).rev().collect();
    let written = items.permuted(&(0..items.len()).collect::<Vec<_>>());
    assert_eq!(written.text, ACCOUNTS);
    let reversed = items.permuted(&order);
    let (a, b) = (written.answer(), reversed.answer());
    assert!(!a.accepted);
    assert_eq!(a, b);
    // The line of the diagnostic changes; its item and offset do not.
    let line = |t: &str| test(t).into_iter().map(|o| o.line).collect::<Vec<_>>();
    assert_ne!(line(&written.text), line(&reversed.text));
}

/// Items that declare one name: `step` is an overload set of two arrows.
const STEPS: &str = "\
step(x: int) = x + 1;
start = 0;
step(x: String) = x ++ \"!\";
main() = 0;
";

#[test]
fn the_declarations_of_a_name_keep_their_written_order() {
    let items = items(STEPS);
    assert_eq!(items.names, [["step"], ["start"], ["step"], ["main"]]);
    let [reversed, shuffled] = items.orders();
    assert_eq!(reversed, [3, 0, 1, 2]);
    for order in [reversed, shuffled] {
        let first = order.iter().position(|&i| i == 0).unwrap();
        let second = order.iter().position(|&i| i == 2).unwrap();
        assert!(first < second, "{order:?}");
    }
}

/// An item that declares two names keeps its place against the other declarations of each:
/// `a, b = (1, 2)` declares `a` and `b`, so it stays before or after `b = 3` as written, in
/// either written order. The unit is rejected, since a scope binds `b` once, and the rejection
/// is at the second binding of `b`, so swapping the two moves it. Keyed by its first name only,
/// `a, b = (1, 2)` was free to move past `b = 3`, and the rejection moved with the swap.
#[test]
fn an_item_of_several_names_keeps_its_order_against_each() {
    for (unit, names) in [
        ("a, b = (1, 2);\nb = 3;\n", [vec!["a", "b"], vec!["b"]]),
        ("b = 3;\na, b = (1, 2);\n", [vec!["b"], vec!["a", "b"]]),
    ] {
        let items = items(unit);
        assert_eq!(items.names, names);
        assert_eq!(items.orders(), [[0, 1], [0, 1]], "{unit}");
        let orders = ["reversed", "shuffled"].into_iter().zip(items.orders());
        check_unit(unit, unit, &items, &orders.collect::<Vec<_>>());
    }
}

/// Names shared along a chain of items join them all, and `_` declares nothing: `c` is free
/// to move, and the three items that declare `a` or `b` keep their written order.
#[test]
fn items_joined_through_shared_names_keep_their_written_order() {
    let unit = "a, _ = (1, 2);\nc = 0;\nb, a = (3, 4);\nb = 5;\n";
    let items = items(unit);
    assert_eq!(
        items.names,
        [vec!["a"], vec!["c"], vec!["b", "a"], vec!["b"]]
    );
    let [reversed, _] = items.orders();
    assert_eq!(reversed, [0, 2, 1, 3]);
}

/// Two incomparable arrows of `f` whose domains overlap on 0 to 10. DESIGN.md writes the second
/// `int[..10]`, which sec:grammar does not parse: a range literal has a lower end, `_` when it
/// has none (`RangeLit`).
const OVERLAP: [&str; 2] = [
    "f(x: int[0..]) -> String = \"a\";\n",
    "f(x: int[_..=10]) -> String = \"b\";\n",
];

/// The unit of the two arrows in `order`, with a test that `f(5)` is `want`.
fn overlap(order: [usize; 2], want: &str) -> String {
    format!(
        "{}{}probe(positional n) = f(n)\ntest {{ 5 -> \"{want}\" }}\n",
        OVERLAP[order[0]], OVERLAP[order[1]]
    )
}

/// The restriction matters: overload dispatch runs the earliest declared of the applicable
/// arrows (rule 6 of sec:type_resolution), so swapping two declarations of one name changes
/// the answer, which is why the permutations keep each name's declarations in written order.
#[test]
#[ignore = "needs overload dispatch (step L2.6) and refinement and result types (layer L10)"]
fn swapping_two_declarations_of_one_name_changes_which_arrow_runs() {
    for (order, want) in [([0, 1], "a"), ([1, 0], "b")] {
        let unit = overlap(order, want);
        let failures: Vec<_> = test(&unit).into_iter().filter_map(|o| o.failure).collect();
        assert!(failures.is_empty(), "{unit}{failures:?}");
    }
}

/// What the two declarations give at L1, in either order: the same two rejections, one in
/// each declaration, at the same offset within it.
#[test]
fn at_l1_the_two_declarations_are_rejected_alike_in_either_order() {
    let unit = overlap([0, 1], "a");
    let items = items(&unit);
    assert_eq!(items.names, [["f"], ["f"], ["probe"]]);
    let [written, swapped] = [[0, 1, 2], [1, 0, 2]].map(|order| items.permuted(&order).answer());
    assert_eq!(written, swapped);
    let messages: Vec<(Place, &str)> = written
        .diagnostics
        .iter()
        .map(|d| (d.at, d.message.as_str()))
        .collect();
    assert_eq!(
        messages,
        [
            ((0, 8), zed_tests::not_yet!("the refinement `[0..]`")),
            ((1, 8), zed_tests::not_yet!("the refinement `[_..=10]`"))
        ]
    );
}

/// A unit with a form of a later layer in each of two items: each item's error is reported,
/// so the diagnostics do not depend on which item comes first. Building stopped at the first
/// item that failed, and the corpus unit `07-json-parser/json.zed` reported its first struct
/// grammar as written and its first `matching` type when reversed.
#[test]
fn each_item_that_cannot_be_built_is_reported() {
    let unit = "\
// A reading in the low range, then one in the high range.
low(r: int[0..=50]) = r;
high(r: int[50..]) = r;
";
    let out = super::rejected(unit);
    assert_eq!(
        out,
        concat!(
            "2:11: ",
            zed_tests::not_yet!("the refinement `[0..=50]`"),
            "\n3:12: ",
            zed_tests::not_yet!("the refinement `[50..]`")
        )
    );
    let items = items(unit);
    let [reversed, _] = items.orders();
    assert_eq!(
        items.permuted(&[0, 1]).answer(),
        items.permuted(&reversed).answer()
    );
}

/// Every order of the items `0..n`, the written one first, by Heap's algorithm with an
/// explicit counter per place. For units of a few items: n! orders.
fn every_order(n: usize) -> Vec<Vec<usize>> {
    let mut order: Vec<usize> = (0..n).collect();
    let mut out = vec![order.clone()];
    let mut c = vec![0; n];
    let mut i = 1;
    while i < n {
        if c[i] < i {
            order.swap(if i % 2 == 0 { 0 } else { c[i] }, i);
            out.push(order.clone());
            c[i] += 1;
            i = 1;
        } else {
            c[i] = 0;
            i += 1;
        }
    }
    out
}

/// `unit` checked in every order of its items against its written order.
fn agrees_in_every_order(name: &str, unit: &str) -> Answer {
    let items = items(unit);
    let orders: Vec<(&str, Vec<usize>)> = (every_order(items.len()).into_iter())
        .map(|o| ("moved", o))
        .collect();
    check_unit(name, unit, &items, &orders);
    items.permuted(&orders[0].1).answer()
}

/// Two functions defined in terms of each other are reported by name, at the first by name,
/// whichever comes first in the unit. The checker reported them in source order at the first
/// in the unit: "`odd`, `even`" at `odd` when `odd` came first.
#[test]
fn a_cycle_is_reported_alike_in_every_order() {
    let unit = "\
// Whether a count is even, counting down.
even(positional n) = if n == 0 { true } else { odd(n - 1) };
odd(positional n) = if n == 0 { false } else { even(n - 1) };
";
    let answer = agrees_in_every_order("even and odd", unit);
    let messages: Vec<(Place, &str)> = (answer.diagnostics.iter())
        .map(|d| (d.at, d.message.as_str()))
        .collect();
    let message = "`even`, `odd` are defined in terms of each other, which is recursion. Recursion \
                   is part of the Zed language, and this version of zedc does not compile it \
                   yet. Write the computation without a definition that uses itself.";
    assert_eq!(messages, [((0, 43), message)]);
}

/// Two separate cycles are both reported, in every order of the four items. The checker
/// reported only the first cycle its search met, which depended on the order.
#[test]
fn every_cycle_is_reported_in_every_order() {
    let unit = "a = b + 1;\nb = a + 1;\nc = d + 1;\nd = c + 1;\n";
    let answer = agrees_in_every_order("two cycles", unit);
    let messages: Vec<(Place, &str)> = (answer.diagnostics.iter())
        .map(|d| (d.at, d.message.as_str()))
        .collect();
    let each = |names| {
        format!(
            "{names} are defined in terms of each other, which is recursion. Recursion is part of \
             the Zed language, and this version of zedc does not compile it yet. Write the \
             computation without a definition that uses itself."
        )
    };
    let (ab, cd) = (each("`a`, `b`"), each("`c`, `d`"));
    assert_eq!(messages, [((0, 0), ab.as_str()), ((2, 0), cd.as_str())]);
}

/// A doc comment after the last item documents no declaration, so it stays at the end of the
/// unit when the items move. Cut with the last item, it documented the next item once moved,
/// and the unit was accepted.
#[test]
fn a_doc_comment_at_the_end_of_the_unit_stays_there() {
    let unit = "\
fee(positional balance) = balance - 2;
tens(positional balance) = balance div 10 * 10;
/// The balance after a year.
";
    let items = items(unit);
    assert_eq!(&unit[items.cuts[2]..], "/// The balance after a year.\n");
    let answer = agrees_in_every_order("a dangling doc comment", unit);
    assert!(!answer.accepted);
    let messages: Vec<(Place, &str)> = (answer.diagnostics.iter())
        .map(|d| (d.at, d.message.as_str()))
        .collect();
    let message = "this doc comment documents no declaration; it is at the end of the unit";
    assert_eq!(messages, [((2, 0), message)]);
}

/// A doc comment at the end of an item's line documents the item that follows, so it is cut
/// with that item.
#[test]
fn a_doc_comment_at_the_end_of_a_line_goes_with_the_next_item() {
    let unit = "low = 1; /// The highest reading.\nhigh = 9;\nspan = high - low;\n";
    let items = items(unit);
    let texts: Vec<&str> = (0..items.len())
        .map(|i| &unit[items.cuts[i]..items.cuts[i + 1]])
        .collect();
    assert_eq!(
        texts,
        [
            "low = 1;",
            " /// The highest reading.\nhigh = 9;\n",
            "span = high - low;\n"
        ]
    );
    assert!(agrees_in_every_order("a doc comment after an item", unit).accepted);
}

/// `n` items: functions, each odd one calling the one before, a test table on every tenth
/// odd one, and a `main`. No call goes deeper than two, so the tables cost O(n).
fn chain(n: usize) -> String {
    let mut src = String::new();
    for i in 0..n {
        let p = i.saturating_sub(1);
        src += &match i % 10 {
            1 => format!("step{i}(positional x) = step{p}(x) + 1\ntest {{ 0 -> {i} }}\n"),
            _ if i % 2 == 1 => format!("step{i}(positional x) = step{p}(x) + 1;\n"),
            _ => format!("step{i}(positional x) = x + {i};\n"),
        };
    }
    src + "main() = 0;\n"
}

/// `n` items over seven names, each owning every seventh item, so keeping each name's written
/// order is exercised on every item.
fn rates(n: usize) -> String {
    (0..n)
        .map(|i| format!("rate{}(positional x) = x + {i};\n", i % 7))
        .collect()
}

/// `n` items, every other one a binding of two names out of eight (`v0` to `v4`, `w0` to
/// `w2`), the rest functions over seven names, so the joins of the bindings grow and merge.
fn pairs(n: usize) -> String {
    (0..n)
        .map(|i| match i % 2 {
            0 => format!("rate{}(positional x) = x + {i};\n", i % 7),
            _ => format!("v{}, w{} = ({i}, {i});\n", i % 5, i % 3),
        })
        .collect()
}

/// Cutting a unit into items is O(i): the lex and parse, and one pass over the root's items.
#[test]
fn cutting_a_unit_into_items_scales() {
    let n = 2000;
    let units: HashMap<usize, String> = [n, 8 * n].into_iter().map(|k| (k, rates(k))).collect();
    scaling::check("cutting n items of seven names", n, |k| {
        assert_eq!(items(&units[&k]).len(), k);
    });
}

/// Moving the items is O(i): the two orders, each name's written order kept, and the moved
/// texts. The items are cut before timing, since the lex and parse would hide a quadratic
/// permutation.
#[test]
fn moving_the_items_of_a_unit_scales() {
    let n = 2000;
    let units: HashMap<usize, String> = [n, 8 * n].into_iter().map(|k| (k, rates(k))).collect();
    let cut: HashMap<usize, Items> = units.iter().map(|(&k, t)| (k, items(t))).collect();
    scaling::check("moving n items of seven names", n, |k| {
        let items = &cut[&k];
        for order in items.orders() {
            assert_eq!(items.permuted(&order).text.len(), units[&k].len());
        }
    });
}

/// Keeping the written order of items that declare several names is O(i): the joins of
/// shared names are found by union-find, with one hash lookup per name.
#[test]
fn moving_items_of_several_names_scales() {
    let n = 2000;
    let units: HashMap<usize, String> = [n, 8 * n].into_iter().map(|k| (k, pairs(k))).collect();
    let cut: HashMap<usize, Items> = units.iter().map(|(&k, t)| (k, items(t))).collect();
    assert_eq!(cut[&n].names[1], ["v1", "w1"]);
    scaling::check("moving n items, every other one of two names", n, |k| {
        let items = &cut[&k];
        for order in items.orders() {
            assert_eq!(items.permuted(&order).text.len(), units[&k].len());
        }
    });
}

#[test]
fn checking_a_unit_with_its_items_moved_scales() {
    let n = 200;
    let units: HashMap<usize, String> = [n, 8 * n].into_iter().map(|k| (k, chain(k))).collect();
    scaling::check(
        "cutting, moving and checking n items, with a test on every tenth",
        n,
        |k| {
            let text = &units[&k];
            let items = items(text);
            let [reversed, _] = items.orders();
            let p = items.permuted(&reversed);
            let answer = p.answer();
            assert!(answer.accepted, "{answer:?}");
            assert_eq!(answer.outcomes.len(), k / 10);
            assert!(answer.outcomes.iter().all(|o| o.1.is_none()), "{answer:?}");
        },
    );
}
