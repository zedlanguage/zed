use std::collections::HashMap;

use super::*;
use crate::seed::Rng;

// Every expected answer below is byte comparison: two strings must get one name exactly when
// their bytes are equal. The canonical name of a string is that of its bytes parsed whole as
// one block (`Names::leaf`), which reads no summary; every other construction joins summaries.

/// A number in `lo..=hi`.
fn int(rng: &mut Rng, lo: usize, hi: usize) -> usize {
    lo + rng.below(hi - lo + 1)
}

/// [`decide`] on labels given as a list.
fn decide_of(ids: &[u128], ts: bool, te: bool) -> Vec<bool> {
    decide(ids.len(), |i| ids[i], ts, te)
}

fn name_of(s: &Option<Arc<Sum>>) -> u64 {
    s.as_ref().map_or(EMPTY, |s| s.name)
}

/// Every name met, with its bytes, and every string met, with its name: a name given to two
/// different strings, or two names to one string, fails.
#[derive(Default)]
struct Corpus {
    by_name: HashMap<u64, Vec<u8>>,
    by_bytes: HashMap<Vec<u8>, u64>,
}

impl Corpus {
    fn add(&mut self, name: u64, data: &[u8]) {
        let bytes = self.by_name.entry(name).or_insert_with(|| data.to_vec());
        assert_eq!(bytes, data, "two strings share the name {name}");
        let n = *self.by_bytes.entry(data.to_vec()).or_insert(name);
        assert_eq!(n, name, "{data:?} has two names");
    }
}

/// `data` as a random tree of joins, leaves of 1 to `leafmax` bytes.
fn build(names: &mut Names, data: &[u8], rng: &mut Rng, leafmax: usize) -> Option<Arc<Sum>> {
    if data.len() <= 1 || (data.len() <= leafmax && rng.next_u64().is_multiple_of(2)) {
        return names.leaf(data);
    }
    let i = int(rng, 0, data.len());
    let x = build(names, &data[..i], rng, leafmax);
    let y = build(names, &data[i..], rng, leafmax);
    names.join(x, y)
}

#[test]
fn names_are_equal_exactly_when_bytes_are() {
    // Every string over {a, b} of up to 12 bytes, split at every place: coin tossing on a
    // two-letter alphabet meets all its cases of labels at short lengths.
    let mut names = Names::new();
    let mut corpus = Corpus::default();
    for n in 0..=12u32 {
        for bits in 0..1u32 << n {
            let data: Vec<u8> = (0..n).map(|i| b'a' + ((bits >> i) & 1) as u8).collect();
            let whole = names.leaf(&data);
            corpus.add(name_of(&whole), &data);
            for i in 0..=data.len() {
                let (x, y) = (names.leaf(&data[..i]), names.leaf(&data[i..]));
                let joined = names.join(x, y);
                corpus.add(name_of(&joined), &data);
            }
        }
    }
}

/// A string of `n` bytes of one of five kinds: random, periodic, periodic with one byte changed,
/// runs, and a Fibonacci word, which is the hardest case for a local parse.
fn adversarial(rng: &mut Rng, n: usize) -> Vec<u8> {
    let all: Vec<u8> = (0..=255).collect();
    let alphabets: [&[u8]; 5] = [b"ab", b"abc", b"a", &all, b"aab"];
    let alpha = rng.pick(&alphabets);
    match rng.below(5) {
        0 => (0..n).map(|_| rng.pick(alpha)).collect(),
        k @ (1 | 2) => {
            let unit: Vec<u8> = (0..int(rng, 1, 7)).map(|_| rng.pick(alpha)).collect();
            let mut data: Vec<u8> = unit.iter().copied().cycle().take(n).collect();
            if k == 2 && n > 0 {
                let i = rng.below(n);
                data[i] = rng.pick(alpha);
            }
            data
        }
        3 => {
            let mut data = Vec::new();
            while data.len() < n {
                let b = rng.pick(alpha);
                data.extend(std::iter::repeat_n(b, int(rng, 1, 40)));
            }
            data.truncate(n);
            data
        }
        _ => {
            let (mut a, mut b) = (b"a".to_vec(), b"ab".to_vec());
            while b.len() < n {
                let next = [&b[..], &a[..]].concat();
                (a, b) = (b, next);
            }
            b.truncate(n);
            b
        }
    }
}

#[test]
fn random_and_adversarial_joins_match_bytes() {
    let mut names = Names::new();
    let mut corpus = Corpus::default();
    let (mut rng, _) = Rng::fresh("random_and_adversarial_joins_match_bytes");
    for _ in 0..150 {
        let n = rng.pick(&[5, 30, 100, 300, 1000, 3000]);
        let data = adversarial(&mut rng, n);
        let whole = names.leaf(&data);
        corpus.add(name_of(&whole), &data);
        for leafmax in [1, 50, 400] {
            let s = build(&mut names, &data, &mut rng, leafmax);
            corpus.add(name_of(&s), &data);
        }
    }
    // Each string with one byte changed, at the start, the middle and the end, differs.
    for n in [40, 400, 4000] {
        let data = adversarial(&mut rng, n);
        for i in [0, n / 2, n - 1] {
            let mut other = data.clone();
            other[i] ^= 1;
            let s = build(&mut names, &other, &mut rng, 50);
            corpus.add(name_of(&s), &other);
        }
        let s = build(&mut names, &data, &mut rng, 50);
        corpus.add(name_of(&s), &data);
    }
}

#[test]
fn zimin_words_built_both_ways_agree() {
    // x(k + 1) = x(k) c(k) x(k), built as (x c) x and as x (c x), 40 times: 2^40 bytes and more.
    // Checked against the bytes while short, and the two associations against each other after.
    let mut names = Names::new();
    let mut corpus = Corpus::default();
    let (mut rng, _) = Rng::fresh("zimin_words_built_both_ways_agree");
    for _ in 0..4 {
        let base: Vec<u8> = (0..int(&mut rng, 1, 40))
            .map(|_| rng.pick(b"abc"))
            .collect();
        let (mut x1, mut x2) = (names.leaf(&base), names.leaf(&base));
        let mut data = base;
        let mut seen = vec![name_of(&x1)];
        for k in 0..40 {
            let c: Vec<u8> = (0..int(&mut rng, 1, 3))
                .map(|_| rng.pick(b"abcd"))
                .collect();
            let (cl, cr) = (names.leaf(&c), names.leaf(&c));
            let left = names.join(x1.clone(), cl);
            let y1 = names.join(left, x2.clone());
            let right = names.join(cr, x2);
            let y2 = names.join(x1, right);
            assert_eq!(name_of(&y1), name_of(&y2), "step {k}");
            if k < 12 {
                data = [&data[..], &c[..], &data[..]].concat();
                corpus.add(name_of(&y1), &data);
                corpus.add(name_of(&names.leaf(&data)), &data);
            }
            // Each step is longer than the one before, so its name is new.
            assert!(!seen.contains(&name_of(&y1)), "step {k}");
            seen.push(name_of(&y1));
            (x1, x2) = (y1, y2);
        }
    }
}

pub(super) fn join(a: &Text, b: &Text) -> Text {
    Text::join(a, b).expect("the test's texts are short of usize::MAX bytes")
}

/// `t` joined to itself `k` times: `2^k` times as long, in `O(k)` nodes.
fn doubled(t: &str, k: u32) -> Text {
    let mut t = Text::from(t);
    for _ in 0..k {
        t = join(&t, &t);
    }
    t
}

#[test]
fn doubled_texts_of_2_to_40_bytes_are_named() {
    // One string of 5 · 2^40 bytes as two trees of different shape, and a string that differs
    // from it in one byte of each copy. A comparison by bytes would read 5 TB.
    let mut names = Names::new();
    let a = doubled("abcab", 40);
    let b = doubled("abcababcab", 39);
    let c = doubled("abcac", 40);
    assert_eq!(a.len(), 5 << 40);
    assert_eq!(names.name(&a), names.name(&b));
    assert_ne!(names.name(&a), names.name(&c));
    // Every doubling is a new string; doublings of the two bases agree a step apart.
    let mut seen = Vec::new();
    for k in 1..=40 {
        let n = names.name(&doubled("abcab", k));
        assert_eq!(n, names.name(&doubled("abcababcab", k - 1)), "k = {k}");
        assert!(!seen.contains(&n), "k = {k}");
        seen.push(n);
    }
}

#[test]
fn texts_joined_in_any_order_have_one_name() {
    // The finger tree's shape follows the order of the joins; the names must not. Pieces of 1 to
    // 300 bytes joined from the left, from the right, and as a balanced tree, and the text read
    // into one block, all one name; one byte changed gives another.
    let (mut rng, _) = Rng::fresh("texts_joined_in_any_order_have_one_name");
    let mut names = Names::new();
    for _ in 0..30 {
        let n = int(&mut rng, 1, 60);
        let pieces: Vec<String> = (0..n)
            .map(|_| {
                let len = int(&mut rng, 1, 300);
                let data = adversarial(&mut rng, len);
                data.iter().map(|&b| char::from(b'a' + b % 26)).collect()
            })
            .collect();
        let texts: Vec<Text> = pieces.iter().map(Text::from).collect();
        let left = texts.iter().fold(Text::from(""), |t, p| join(&t, p));
        let right = texts.iter().rev().fold(Text::from(""), |t, p| join(p, &t));
        fn balanced(ts: &[Text]) -> Text {
            match ts {
                [] => Text::from(""),
                [t] => t.clone(),
                _ => join(
                    &balanced(&ts[..ts.len() / 2]),
                    &balanced(&ts[ts.len() / 2..]),
                ),
            }
        }
        let mid = balanced(&texts);
        let flat = Text::from(pieces.concat());
        let want = names.name(&flat);
        assert_eq!(names.name(&left), want);
        assert_eq!(names.name(&right), want);
        assert_eq!(names.name(&mid), want);
        let mut other = pieces.concat().into_bytes();
        let i = rng.below(other.len());
        other[i] = if other[i] == b'a' { b'b' } else { b'a' };
        let other = String::from_utf8(other).expect("ASCII");
        assert_ne!(names.name(&Text::from(other)), want);
    }
    assert_eq!(names.name(&Text::from("")), Name(EMPTY));
}

/// `ids` with no two neighbors equal: each id is drawn wide (any 64 bits) or narrow (below 8),
/// so the coin-tossing rounds see both small and large first differing bits.
fn proper_ids(rng: &mut Rng, n: usize) -> Vec<u128> {
    let mut ids: Vec<u128> = Vec::with_capacity(n);
    while ids.len() < n {
        let id = u128::from(if rng.next_u64().is_multiple_of(2) {
            rng.next_u64()
        } else {
            rng.below_u64(8)
        });
        if ids.last() != Some(&id) {
            ids.push(id);
        }
    }
    ids
}

/// A block start at `i` reads `ids[i - 8 ..= i + 4]` and nothing else ([`CL`], [`CR`]), with
/// ids of any width. The pairs below, from round 1 of the cross-review of item
/// STAGE-joined-eq-build, differ at one position only and give a different decision at `i`:
/// one at `i + 4`, so 3 to the right is too few (the block ids the other tests make are
/// numbered in order, small, and never reach that case), and one at `i - 7`. A random change
/// almost never shows either, so the pairs are kept as written.
#[test]
fn a_block_start_reads_8_symbols_left_and_4_right() {
    let x = [
        3186582064, 1108385231, 3186582064, 1108435504, 2565628464, 955015728, 3102499376,
        15491632, 3236717104, 929849904, 1247169940, 1851149716, 2473168930, 1287098402,
        2897711138, 1397256157, 2897711138,
    ];
    let mut y = x;
    y[14] = 2964820002;
    assert_ne!(
        decide_of(&x, false, false)[10],
        decide_of(&y, false, false)[10]
    );
    let (i, j) = (10, 14);
    assert!(j - i <= CR, "a start reads 4 to its right");
    let x = [
        165, 9, 71, 129, 112, 206, 218, 248, 48, 246, 71, 128, 231, 42, 57, 15, 152, 221, 59, 137,
        69, 216, 171, 30,
    ];
    let mut y = x;
    y[5] = 188;
    assert_ne!(
        decide_of(&x, false, false)[12],
        decide_of(&y, false, false)[12]
    );
    let (i, j) = (12, 5);
    assert!(i - j <= CL, "a start reads 7 to its left");

    // A change outside `i - 8 ..= i + 4` leaves the start at `i` as it was.
    let (mut rng, _) = Rng::fresh("a_block_start_reads_8_symbols_left_and_4_right");
    for _ in 0..20_000 {
        let n = int(&mut rng, 14, 40);
        let ids = proper_ids(&mut rng, n);
        let i = int(&mut rng, CL, n - 1 - CR);
        let outside: Vec<usize> = (0..n).filter(|&j| j + CL < i || j > i + CR).collect();
        if outside.is_empty() {
            continue;
        }
        let j = rng.pick(&outside);
        let mut z = ids.clone();
        z[j] = loop {
            let id = u128::from(rng.next_u64());
            if Some(&id) != j.checked_sub(1).map(|k| &ids[k]) && Some(&id) != ids.get(j + 1) {
                break id;
            }
        };
        let (a, b) = (
            decide_of(&ids, false, false)[i],
            decide_of(&z, false, false)[i],
        );
        assert_eq!(a, b, "{ids:?} at {i}, {j} changed");
    }
}

/// The block starts as the module's comment states them, one round or pass at a time over the
/// whole list: the form [`decide`] had before it ran the rounds in one pass and the passes in
/// another (row PERF-canon-flat-strings).
fn plain_decide(ids: &[u128], ts: bool, te: bool) -> Vec<bool> {
    let n = ids.len();
    let toss = |x: u128, left: Option<u128>| -> u128 {
        let p = left.map_or(0, |l| (x ^ l).trailing_zeros());
        u128::from(2 * p) + ((x >> p) & 1)
    };
    let mut lab: Vec<u128> = ids.to_vec();
    for _ in 0..4 {
        lab = (0..n)
            .map(|i| toss(lab[i], i.checked_sub(1).map(|j| lab[j])))
            .collect();
    }
    for c in [5, 4, 3] {
        for i in 0..n {
            if lab[i] == c {
                let left = i.checked_sub(1).map(|j| lab[j]);
                let right = lab.get(i + 1).copied();
                lab[i] = (0..3)
                    .find(|&v| Some(v) != left && Some(v) != right)
                    .expect("three labels, two neighbors");
            }
        }
    }
    let mut st: Vec<bool> = (0..n)
        .map(|i| {
            let left = i.checked_sub(1).map(|j| lab[j]);
            let right = lab.get(i + 1).copied();
            left.is_none_or(|l| lab[i] > l) && right.is_none_or(|r| lab[i] > r)
        })
        .collect();
    if ts {
        st[0] = true;
        if n > 1 {
            st[1] = false;
        }
    }
    if te && n > 1 {
        st[n - 1] = false;
    }
    st
}

/// [`decide`] gives the starts of the plain rounds and passes, on lists of every length from 1
/// to 60, wide and narrow labels, at each choice of true start and end.
#[test]
fn decide_gives_the_starts_of_the_plain_rounds() {
    let (mut rng, _) = Rng::fresh("decide_gives_the_starts_of_the_plain_rounds");
    for _ in 0..20_000 {
        let n = int(&mut rng, 1, 60);
        let ids = proper_ids(&mut rng, n);
        for (ts, te) in [(false, false), (true, false), (false, true), (true, true)] {
            assert_eq!(
                decide_of(&ids, ts, te),
                plain_decide(&ids, ts, te),
                "{ids:?} {ts} {te}"
            );
        }
    }
}

/// Inner blocks hold 2 to 4 symbols, but the forced start and end can make a block at the
/// true end hold 5 (round 1 of the cross-review of item STAGE-joined-eq-build), within
/// [`MAX_BLOCK`].
#[test]
fn a_block_at_the_true_end_may_hold_5_symbols() {
    let ids = [
        47, 115, 227, 95, 163, 55, 37, 178, 23, 170, 184, 118, 63, 8, 95, 125, 194, 112, 183, 75,
        15, 181, 9, 37,
    ];
    let st = decide_of(&ids, true, true);
    let starts: Vec<usize> = (0..ids.len()).filter(|&i| st[i]).collect();
    assert_eq!(starts, [0, 3, 5, 8, 10, 12, 14, 17, 19]);
    assert_eq!(ids.len() - 19, 5);
    let (mut rng, _) = Rng::fresh("a_block_at_the_true_end_may_hold_5_symbols");
    for _ in 0..20_000 {
        let n = int(&mut rng, 2, 60);
        let ids = proper_ids(&mut rng, n);
        let st = decide_of(&ids, true, true);
        let mut starts: Vec<usize> = (0..n).filter(|&i| st[i]).collect();
        starts.push(n);
        assert!(
            starts.windows(2).all(|w| w[1] - w[0] <= MAX_BLOCK),
            "{ids:?}"
        );
    }
}

/// A 128-bit hash for the label tests (two FNV-1a passes with different starts); its quality
/// does not matter, since a collision only makes [`Names::collided`] true.
fn fnv128(data: &[u8]) -> u128 {
    let pass = |start: u64| {
        data.iter().fold(start, |h, &b| {
            (h ^ u64::from(b)).wrapping_mul(0x100_0000_01b3)
        })
    };
    u128::from(pass(0xcbf2_9ce4_8422_2325)) << 64 | u128::from(pass(0x84222325_cbf29ce4))
}

/// The rules under `n` written out by content, each child by its own form: equal for two
/// names, in any two dictionaries, exactly when the rules [`Names::part`] gives are the same
/// tree. Also returns the bytes, to check the rules spell the text.
fn form(names: &Names, n: Name, memo: &mut HashMap<Name, (String, Vec<u8>)>) -> (String, Vec<u8>) {
    if let Some(f) = memo.get(&n) {
        return f.clone();
    }
    let f = match names.part(n) {
        Part::Empty => (String::from("E"), Vec::new()),
        Part::Byte(b) => (format!("{b}"), vec![b]),
        Part::Run(x, count) => {
            let (s, bytes) = form(names, x, memo);
            (format!("R{count}({s})"), bytes.repeat(count as usize))
        }
        Part::Block(xs) => {
            let parts: Vec<_> = xs.iter().map(|&x| form(names, x, memo)).collect();
            let s: Vec<&str> = parts.iter().map(|p| p.0.as_str()).collect();
            let bytes = parts.iter().flat_map(|p| p.1.iter().copied()).collect();
            (format!("B({})", s.join(",")), bytes)
        }
    };
    memo.insert(n, f.clone());
    f
}

#[test]
fn canonical_parts_are_a_function_of_the_text() {
    // Each text named in two canonical dictionaries: one that met other texts first and reads
    // it whole, one that builds it as a random tree of joins. The rules under the two names
    // must be the same tree and spell the text; names stay exact as in `Names::new`.
    let (mut rng, _) = Rng::fresh("canonical_parts_are_a_function_of_the_text");
    let mut warm = Names::canonical(fnv128);
    let mut corpus = Corpus::default();
    for _ in 0..120 {
        let n = rng.pick(&[1, 5, 30, 100, 300, 1000, 3000]);
        let noise = adversarial(&mut rng, n);
        let _ = warm.leaf(&noise);
        let data = adversarial(&mut rng, n);
        let a = warm.leaf(&data);
        corpus.add(name_of(&a), &data);
        let mut fresh = Names::canonical(fnv128);
        let leafmax = rng.pick(&[1, 50, 400]);
        let b = build(&mut fresh, &data, &mut rng, leafmax);
        let fa = form(&warm, Name(name_of(&a)), &mut HashMap::new());
        let fb = form(&fresh, Name(name_of(&b)), &mut HashMap::new());
        assert_eq!(fa.1, data, "the rules spell the text");
        assert_eq!(fa, fb, "{data:?}");
        assert!(!fresh.collided());
    }
    assert!(!warm.collided());
    // A text of 5 · 2^40 bytes doubled from two bases: one tree of rules, in O(levels) rules.
    let mut x = Names::canonical(fnv128);
    let mut y = Names::canonical(fnv128);
    let a = x.name(&doubled("abcab", 40));
    let b = y.name(&doubled("abcababcab", 39));
    // The bytes are 5 TB, so only the trees of rules are compared.
    fn shape(names: &Names, n: Name, memo: &mut HashMap<Name, String>) -> String {
        if let Some(s) = memo.get(&n) {
            return s.clone();
        }
        let s = match names.part(n) {
            Part::Empty => String::from("E"),
            Part::Byte(b) => format!("{b}"),
            Part::Run(x, count) => format!("R{count}({})", shape(names, x, memo)),
            Part::Block(xs) => {
                let s: Vec<String> = xs.iter().map(|&x| shape(names, x, memo)).collect();
                format!("B({})", s.join(","))
            }
        };
        memo.insert(n, s.clone());
        s
    }
    let (sa, sb) = (
        shape(&x, a, &mut HashMap::new()),
        shape(&y, b, &mut HashMap::new()),
    );
    assert_eq!(sa, sb);
    assert!(!x.collided() && !y.collided());
}

/// The next `k` bits of an exact label's code, most significant first.
struct Bits {
    code: u128,
    left: u32,
}

impl Bits {
    fn take(&mut self, k: u32) -> u128 {
        self.left -= k;
        (self.code >> self.left) & ((1u128 << k) - 1)
    }

    /// The form ([`form`]'s first half) of the symbol whose code comes next.
    fn symbol(&mut self) -> String {
        if self.take(1) == 0 {
            format!("{}", self.take(8))
        } else {
            self.rule()
        }
    }

    /// The form of the rule whose code comes next.
    fn rule(&mut self) -> String {
        if self.take(1) == 0 {
            let s = self.symbol();
            let mut zeros = 0;
            while self.take(1) == 0 {
                zeros += 1;
            }
            format!("R{}({s})", 1u128 << zeros | self.take(zeros))
        } else {
            let k = self.take(3) + 1;
            let s: Vec<String> = (0..k).map(|_| self.symbol()).collect();
            format!("B({})", s.join(","))
        }
    }
}

#[test]
fn an_exact_label_reads_back_to_its_rule() {
    // PERF-canon-flat-strings: a rule whose code fits in 125 bits is labeled by the code, not
    // a hash. Read each such label back, from its bits alone, to the rule's tree, and check
    // that no two rules share a label of any kind.
    let (mut rng, _) = Rng::fresh("an_exact_label_reads_back_to_its_rule");
    let mut names = Names::canonical(fnv128);
    for _ in 0..60 {
        let n = rng.pick(&[5, 30, 300, 3000]);
        let data = adversarial(&mut rng, n);
        let _ = build(&mut names, &data, &mut rng, 50);
    }
    // Long runs, whose counts take long gamma codes, of a byte and of a rule.
    let _ = names.leaf(&[b'a'; 100_000]);
    let _ = names.leaf(&b"ab".repeat(50_000));
    let of = &names.labels.as_ref().expect("a canonical dictionary").of;
    let mut memo = HashMap::new();
    let mut exact = 0;
    for (i, &label) in of.iter().enumerate() {
        if label >> 126 != 1 {
            assert!(
                label >> 127 == 1,
                "a label is exact or hashed, with no collision"
            );
            continue;
        }
        exact += 1;
        let rest = label & !(3 << 126);
        let len = 127 - rest.leading_zeros();
        let mut bits = Bits {
            code: rest & ((1 << len) - 1),
            left: len,
        };
        let read = bits.rule();
        assert_eq!(bits.left, 0, "the code is read to its end");
        let n = Name(FIRST_RULE + i as u64);
        assert_eq!(read, form(&names, n, &mut memo).0);
    }
    let distinct: std::collections::HashSet<u128> = of.iter().copied().collect();
    assert_eq!(distinct.len(), of.len());
    assert!(exact > 0 && exact < of.len(), "{exact} of {}", of.len());
}

#[test]
fn a_weak_label_hash_is_flagged_and_names_stay_exact() {
    // Every hashed label is one value, so neighbors' labels agree wherever two rules too long
    // for an exact label meet: the dictionary says so, and parses by its numbers there, so
    // names stay exact.
    let mut names = Names::canonical(|_| 0);
    let mut corpus = Corpus::default();
    // A text built to reach the hash, so that the collision does not rest on the draws below
    // (row FAIL-canon-collision-test-exact-labels). Its 256 bytes are all different, so no
    // level of its parse holds a run (two neighbors stand for texts with no byte in common),
    // and a rule standing for m bytes has a 9-bit code for each of them: for m ≥ 14 its code
    // passes 125 bits and its label is hashed. Its name is a block of 2 to 6 symbols, so it
    // and its largest part, of at least 43 bytes, are two different hashed rules.
    let distinct: Vec<u8> = (0..=255).collect();
    let whole = names.leaf(&distinct);
    corpus.add(name_of(&whole), &distinct);
    assert!(names.collided());
    let (mut rng, _) = Rng::fresh("a_weak_label_hash_is_flagged_and_names_stay_exact");
    for _ in 0..60 {
        let n = rng.pick(&[5, 30, 300, 3000]);
        let data = adversarial(&mut rng, n);
        let whole = names.leaf(&data);
        corpus.add(name_of(&whole), &data);
        let s = build(&mut names, &data, &mut rng, 50);
        corpus.add(name_of(&s), &data);
    }
    assert!(names.collided());
    assert!(!Names::new().collided());
}
