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
/// white space and a `//` comment, such as a `// ✗` mark. The text before the first item goes
/// with it, and the text after the last with that one.
struct Items<'t> {
    text: &'t str,
    cuts: Vec<usize>,
    /// The name each item declares: the first name of its declaration; `None` for a unit
    /// annotation.
    names: Vec<Option<&'t str>>,
}

/// The items of `text`; one item, the whole text, when it does not lex or parse.
fn items(text: &str) -> Items<'_> {
    let whole = Items {
        text,
        cuts: vec![0, text.len()],
        names: vec![None],
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
    *cuts.last_mut().expect("an item") = text.len();
    Items { text, cuts, names }
}

/// The end of the line from byte `at` of `text`, its line break included, when the rest of the
/// line is white space and at most a `//` comment; otherwise `at`.
fn line_rest(text: &str, at: usize) -> usize {
    let rest = &text[at..];
    let blank = rest.trim_start_matches([' ', '\t']);
    let after = at + rest.len() - blank.len();
    if blank.starts_with("//") || blank.starts_with('\n') || blank.is_empty() {
        text[after..]
            .find('\n')
            .map_or(text.len(), |i| after + i + 1)
    } else {
        at
    }
}

/// The first name of the declaration of item node `item`: its first name token outside its
/// annotations, found in pre-order with an explicit stack; `None` for a unit annotation.
fn declared<'t>(
    text: &'t str,
    tokens: &[zedc::lex::Token],
    tree: &Tree,
    item: usize,
) -> Option<&'t str> {
    let mut stack = vec![item];
    while let Some(n) = stack.pop() {
        match tree.name(n) {
            "Annot" | "UnitAnnot" => continue,
            "Name" => {
                let t = &tokens[tree.nodes[n].start];
                assert!(matches!(t.tok, Tok::Name(_)), "a `Name` node is a name");
                return Some(&text[t.span.start..t.span.end]);
            }
            _ => stack.extend(tree.nodes[n].kids.iter().rev()),
        }
    }
    None
}

impl<'t> Items<'t> {
    fn len(&self) -> usize {
        self.names.len()
    }

    /// `order` with the items of each name put back in their written order: the places the
    /// items of a name take in `order` are given to them in written order. O(i).
    fn keep_names(&self, order: Vec<usize>) -> Vec<usize> {
        let mut written: HashMap<&str, VecDeque<usize>> = HashMap::new();
        for (i, name) in self.names.iter().enumerate() {
            if let Some(name) = name {
                written.entry(name).or_default().push_back(i);
            }
        }
        order
            .into_iter()
            .map(|i| match self.names[i] {
                Some(name) => written
                    .get_mut(name)
                    .and_then(VecDeque::pop_front)
                    .expect("one place per item of the name"),
                None => i,
            })
            .collect()
    }

    /// The reversed order and one seeded shuffle, each keeping each name's written order.
    fn orders(&self) -> [Vec<usize>; 2] {
        let reversed = (0..self.len()).rev().collect();
        let mut shuffled: Vec<usize> = (0..self.len()).collect();
        let mut rng = Rng::new(SEED);
        for i in (1..shuffled.len()).rev() {
            shuffled.swap(i, rng.below(i + 1));
        }
        [self.keep_names(reversed), self.keep_names(shuffled)]
    }

    /// The text with its items in `order`, each followed by a line break when it ends without
    /// one, and where each item starts in it. The written order gives the text unchanged.
    fn permuted(&self, order: &[usize]) -> Permuted {
        let mut text = String::with_capacity(self.text.len() + order.len());
        let mut starts = Vec::with_capacity(order.len());
        for &i in order {
            starts.push((text.len(), i));
            text += &self.text[self.cuts[i]..self.cuts[i + 1]];
            if order.len() > 1 && !text.ends_with('\n') {
                text.push('\n');
            }
        }
        Permuted { text, starts }
    }
}

/// A permuted text, and the start of each item in it, in increasing order, with the item.
struct Permuted {
    text: String,
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
        let said = |d: &zedc::run::Diagnostic| Said {
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
fn units() -> Vec<(String, String)> {
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

/// Checks the units of `units` whose index is `piece` modulo `pieces`, each as written,
/// reversed and shuffled, and returns how many had more than one item.
fn check_piece(units: &[(String, String)], piece: usize, pieces: usize) -> usize {
    let mut moved = 0;
    for (name, text) in units.iter().skip(piece).step_by(pieces) {
        let items = items(text);
        let written = Permuted {
            text: text.clone(),
            starts: items.cuts[..items.len()].iter().copied().zip(0..).collect(),
        };
        let want = across_items_by_verdict(written.answer(), name);
        if items.len() > 1 {
            moved += 1;
        }
        for (how, order) in ["reversed", "shuffled"].into_iter().zip(items.orders()) {
            let p = items.permuted(&order);
            let got = across_items_by_verdict(p.answer(), name);
            assert_eq!(
                want, got,
                "{name}: the items {how}, in the order {order:?}:\n{}",
                p.text
            );
        }
    }
    moved
}

/// The pieces the units are checked in, each a test of its own, so each runs in parallel and
/// within the time of one piece of the suite.
const PIECES: usize = 4;

fn piece(i: usize) {
    let units = units();
    assert!(units.len() >= 60, "{} units", units.len());
    let moved = check_piece(&units, i, PIECES);
    assert!(moved > 0, "piece {i}: no unit of more than one item");
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
    assert_eq!(items.names, [Some("fee"), Some("deposit"), Some("tens")]);
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
    assert_eq!(items.names, [Some("low"), Some("high"), Some("span")]);
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
    assert_eq!(
        items.names,
        [Some("step"), Some("start"), Some("step"), Some("main")]
    );
    let [reversed, shuffled] = items.orders();
    assert_eq!(reversed, [3, 0, 1, 2]);
    for order in [reversed, shuffled] {
        let first = order.iter().position(|&i| i == 0).unwrap();
        let second = order.iter().position(|&i| i == 2).unwrap();
        assert!(first < second, "{order:?}");
    }
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
    assert_eq!(items.names, [Some("f"), Some("f"), Some("probe")]);
    let [written, swapped] = [[0, 1, 2], [1, 0, 2]].map(|order| items.permuted(&order).answer());
    assert_eq!(written, swapped);
    let messages: Vec<(Place, &str)> = written
        .diagnostics
        .iter()
        .map(|d| (d.at, d.message.as_str()))
        .collect();
    let refinement = "this form (TypeSuffix) is built from layer L10";
    assert_eq!(messages, [((0, 8), refinement), ((1, 8), refinement)]);
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
        "2:11: this form (TypeSuffix) is built from layer L10\n\
         3:12: this form (TypeSuffix) is built from layer L10"
    );
    let items = items(unit);
    let [reversed, _] = items.orders();
    assert_eq!(
        items.permuted(&[0, 1]).answer(),
        items.permuted(&reversed).answer()
    );
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

/// Cutting a unit into items and moving them is O(i), measured apart from checking, whose cost
/// would hide a quadratic permutation. Seven names each own every seventh item, so keeping each
/// name's written order is exercised on every item. At 1000 items the parse still hid a quadratic
/// permutation (23 times the work); at 2000 it shows (32 times).
#[test]
fn cutting_and_moving_the_items_of_a_unit_scales() {
    let n = 2000;
    let units: HashMap<usize, String> = [n, 8 * n]
        .into_iter()
        .map(|k| {
            let text = (0..k)
                .map(|i| format!("rate{}(positional x) = x + {i};\n", i % 7))
                .collect();
            (k, text)
        })
        .collect();
    scaling::check("cutting and moving n items of seven names", n, |k| {
        let items = items(&units[&k]);
        assert_eq!(items.len(), k);
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
