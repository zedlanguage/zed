//! Canonical names of texts: one number per text, the same for equal texts and different for
//! different ones, shared by every text named through one [`Names`] (item STAGE-joined-eq-build;
//! docs/joined-strings-study.md). Staging keys its tables by these names, so that two calls at
//! equal joined strings are found equal without reading the strings.
//!
//! The method is the signature encoding of Mehlhorn, Sundar and Uhrig ("Maintaining dynamic
//! sequences under equality tests in polylogarithmic time", Algorithmica 17, 1997), with the
//! block rule of Alstrup, Brodal and Rauhe ("Pattern matching in dynamic texts", SODA 2000).
//! Level 0 of a text is its bytes. Each level is turned into the next in two steps:
//!
//! 1. Runs: each maximal run of one symbol `a`, `k ≥ 2` times, becomes one symbol, the name of
//!    the rule (run, `a`, `k`). After this no two neighbors are equal.
//! 2. Blocks: four rounds of deterministic coin tossing (Cole and Vishkin) give each position a
//!    label in 0..=5, neighbors different; three passes bring the labels to 0..=2; a block
//!    starts at each strict local maximum of the labels. Each block of symbols becomes one
//!    symbol, the name of the rule (block, its symbols).
//!
//! The dictionary gives each new rule the next free number, so a name is a function of the
//! text alone: equal texts get one name, and different texts different names, since a name's
//! rule reads back to its text. That holds whatever the constants below; the constants decide
//! only whether the join of two summaries ([`Names::join`]) gives the name of the whole text,
//! and the tests check it against byte comparison.
//!
//! Locality: whether a block starts at position `i` reads only the symbols `i − 8 ..= i + 4`
//! (four rounds read one left neighbor each, the three passes one on each side, and a maximum
//! one more on each side). Position 0 tosses with `p = 0`, and its label still differs from
//! position 1's: position 1 differs from position 0 in bit `p ≥ 0`, and if `p = 0` the two
//! labels differ in their low bit, else in the bits above it. At a true start the parse puts a
//! start at position 0 and none at 1; at a true end, none at the last position.
//!
//! The parse reads the numbers the dictionary gave, so in a dictionary made by [`Names::new`]
//! the blocks of a text, though not its being equal to another, depend on what the dictionary
//! met before. A dictionary made by [`Names::canonical`] (item CANON-term-string-nodes) gives
//! the coin tossing a label in place of each number: a byte's label is the byte, and a rule's
//! the given hash of its kind, its count or length and its parts' labels, with the top bit set.
//! A label is then a function of the bytes the symbol stands for, so the blocks, and the rules
//! that hold a text's parse ([`Names::part`]), are a function of the text alone, whatever
//! texts, trees and order the dictionary met. The proofs above read of the numbers only that
//! they are fixed for each symbol and that two different symbols have different ones. A label
//! is fixed for each symbol when its rule is made; a rule whose label another rule already
//! holds (two rules whose hashes agree in 128 bits) gets its number as its label instead,
//! which no other symbol holds (a number is at least 256, so no byte's, and below 2^64, so no
//! hashed label's), and [`Names::collided`] says so. The labels are therefore different for
//! different symbols in every case, the proofs hold as written, and the names stay exact; only
//! the claim that the parse is the text's alone is lost on a collision. (A label chosen per
//! window, by whether two neighbors in it collide, would not do: a block start would then
//! read the whole window, not `i − 8 ..= i + 4`, and a join could name one text twice. The
//! test `a_weak_label_hash_is_flagged_and_names_stay_exact` found exactly that.)
//!
//! A text is held as a summary ([`Sum`]): at each level, the part of the sequence that does not
//! depend on what is joined to either side (the middle), as run-length entries, kept whole when
//! short and as its first and last [`K`] entries when long, and the number of entries between
//! the middle and the true parse's next block start on each side (the skips). The join of two
//! summaries parses again, at each level, only the windows where an end meets the middle.

use hashbrown::HashTable;
use hashbrown::hash_table::Entry;
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use std::hash::BuildHasher;
use std::sync::Arc;

use super::tree::{Text, Tree};

/// How many symbols to the left a block start reads.
const CL: usize = 8;
/// How many symbols to the right a block start reads.
const CR: usize = 4;
/// The entries kept at each end of a long middle: at least `lskip + CR` and `rskip + CL` for the
/// largest skips a middle has (`lskip ≤ 12`, `rskip ≤ 9`), so `max(12 + 4, 9 + 8)` = 17. With 16
/// the join reads past a kept end (the negative control of the study's prototype).
const K: usize = 17;
/// The most symbols one block holds. Between two maxima of labels in 0..=2, neighbors different,
/// lie at most three positions (2, 1, 0, 1, 2), so an inner block holds at most 4. A true start
/// drops a start at position 1 and a true end one at the last position, each adding up to the
/// next block; a string short enough that both reach one block, labels `x 2 1 0 1 2`, gives 6.
const MAX_BLOCK: usize = 6;
/// The name of the empty text, which no rule has.
const EMPTY: u64 = u64::MAX;
/// The first number the dictionary gives: below it, each byte is its own name.
const FIRST_RULE: u64 = 256;

/// The canonical name of a text in one [`Names`]: equal texts have one name, different texts
/// different names. The order of names is the order the dictionary met them in, never that of
/// the texts, so it orders a map but says nothing about the bytes.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Name(u64);

impl Name {
    /// The place of the rule this name stands for among the rules its dictionary made, `0` for
    /// the first and so on, none for a byte or the empty text: a table over a dictionary's
    /// rules can be a list indexed by it.
    pub fn rule_index(self) -> Option<usize> {
        match self.0.checked_sub(FIRST_RULE) {
            Some(i) if self.0 != EMPTY => Some(i as usize),
            _ => None,
        }
    }
}

/// A rule of the dictionary: a run of one symbol, or a block of 1 to [`MAX_BLOCK`] symbols, the
/// unused places 0.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Rule {
    Run(u64, u64),
    Block(u8, [u64; MAX_BLOCK]),
}

/// A run-length entry: `count` copies of the symbol `sym`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Ent {
    sym: u64,
    count: u64,
}

/// The middle of one level of a summary.
enum Mid {
    /// At most `2K` entries, all of them.
    Full(Vec<Ent>),
    /// More than `2K` entries: the first `K`, the last `K`, and how many there are.
    Long {
        head: Vec<Ent>,
        tail: Vec<Ent>,
        count: usize,
    },
}

/// One level of a summary: its middle, none when the text has none at this level, and, when it
/// has one, the entries from the middle's start to the first block start the parse of every text
/// that holds this one keeps (`lskip`), and from the last such start to the middle's end
/// (`rskip`). The skips are none at the level that names the text.
struct Level {
    mid: Option<Mid>,
    lskip: Option<usize>,
    rskip: Option<usize>,
}

/// The summary of a nonempty text: its levels from the bytes up, and its name.
struct Sum {
    levels: Vec<Level>,
    name: u64,
}

/// A piece of a middle while a join is parsed: entries, or the long middle of a summary's level.
enum Seg {
    Ents(Vec<Ent>),
    Mid(Arc<Sum>, usize),
}

/// What one level gives: the text's name, or the next level as the entries before its middle,
/// the middle and the entries after, with this level's skips.
enum Step {
    Name(u64),
    Next {
        lskip: Option<usize>,
        rskip: Option<usize>,
        p: Vec<Ent>,
        segs: Vec<Option<Seg>>,
        q: Vec<Ent>,
    },
}

/// The ends of a long middle, with its skips.
struct Long<'a> {
    head: &'a [Ent],
    tail: &'a [Ent],
    count: usize,
    lskip: usize,
    rskip: usize,
}

/// The dictionary of rules, and the summary of each text node named through it.
// Complexity tradeoff: the naive test of two texts' equality reads both, O(N) for texts of N
// bytes, and a doubled text of k nodes is 2^k bytes long, so a table keyed by text reads each key
// whole at every lookup. Here each distinct node of a text is summarized once, from its parts'
// summaries, by parsing again a window of O(K) entries at each of its O(log N) levels: O(n log N)
// dictionary steps for a text of n distinct nodes, each a hash lookup of O(1) expected time, and
// a block of b bytes parsed once in O(b). Tradeoff: O(K log L) words kept per node of length L, a
// memo entry per node that keeps the node alive while the `Names` lives, and names ordered by
// first meeting, not by bytes. Nothing is refused. Tests `names_are_equal_exactly_when_bytes_are`,
// `doubled_texts_of_2_to_40_bytes_are_named`, `naming_n_and_8n_nodes`.
//
// The tables hash with FxHash, not the standard SipHash: their keys are the dictionary's own
// numbers and rules, and addresses of nodes, never chosen by an adversary to collide in a table
// (the canonical parse reads labels, never these hashes), and SipHash was a fifth of the work of
// a flat string (row PERF-canon-flat-strings). Each rule is kept once, in `rules`, and the table
// that finds it holds its place there, a word, where a map from rules to numbers held the rule
// again in each 64-byte slot.
#[derive(Default)]
pub struct Names {
    /// The rule of each number from [`FIRST_RULE`] on, in order.
    rules: Vec<Rule>,
    /// The places in `rules`, found by the FxHash of the rule.
    find: HashTable<usize>,
    // The address of a node's tree, kept alive by the `Text` beside it, names the node for
    // identity only, never for order.
    memo: FxHashMap<usize, (Text, Option<Arc<Sum>>)>,
    /// The labels the parse reads, in a dictionary made by [`Names::canonical`].
    labels: Option<Labels>,
}

/// The content labels of a canonical dictionary ([`Names::canonical`]).
struct Labels {
    hash: fn(&[u8]) -> u128,
    /// The label of each number from [`FIRST_RULE`] on, in order.
    of: Vec<u128>,
    /// The hashed labels given so far.
    held: FxHashSet<u128>,
    /// Whether a rule got its number as its label, its hash being held by another.
    collided: bool,
}

impl Labels {
    /// The label of the symbol `sym`: a byte is its own, a rule the one it was given.
    fn label(&self, sym: u64) -> u128 {
        match sym.checked_sub(FIRST_RULE) {
            None => u128::from(sym),
            Some(i) => self.of[i as usize],
        }
    }

    /// The label of a new rule: the hash of its kind (0 a run, 1 a block), its count or length,
    /// and its parts' labels, little-endian, with the top bit set, so that it is never a
    /// byte's. Its parts were numbered before it, so their labels are known.
    fn of_rule(&self, r: &Rule) -> u128 {
        let mut buf = [0u8; 2 + 8 + 16 * MAX_BLOCK];
        let n = match r {
            Rule::Run(sym, count) => {
                buf[1..9].copy_from_slice(&count.to_le_bytes());
                buf[9..25].copy_from_slice(&self.label(*sym).to_le_bytes());
                25
            }
            Rule::Block(len, syms) => {
                buf[0] = 1;
                buf[1] = *len;
                for (i, &s) in syms[..usize::from(*len)].iter().enumerate() {
                    buf[2 + 16 * i..18 + 16 * i].copy_from_slice(&self.label(s).to_le_bytes());
                }
                2 + 16 * usize::from(*len)
            }
        };
        (self.hash)(&buf[..n]) | 1 << 127
    }
}

/// What a name stands for in a canonical dictionary ([`Names::part`]).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Part {
    /// The empty text.
    Empty,
    /// One byte.
    Byte(u8),
    /// `count` copies of a name's text, `count ≥ 2`.
    Run(Name, u64),
    /// The texts of 1 to 6 names, in order.
    Block(Parts),
}

/// The 1 to 6 names of a block, in order, held in place: [`Names::part`] is asked once or twice
/// for each rule a string writes, and a list on the heap cost an allocation each time (row
/// PERF-canon-flat-strings).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Parts {
    len: u8,
    names: [Name; MAX_BLOCK],
}

impl std::ops::Deref for Parts {
    type Target = [Name];

    fn deref(&self) -> &[Name] {
        &self.names[..usize::from(self.len)]
    }
}

impl std::fmt::Debug for Names {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Names")
            .field("rules", &self.rules.len())
            .field("nodes", &self.memo.len())
            .field("canonical", &self.labels.is_some())
            .finish()
    }
}

impl Names {
    /// An empty dictionary.
    pub fn new() -> Self {
        Self::default()
    }

    /// An empty dictionary whose parse reads content labels made with `hash` (the module's
    /// comment): the rules [`Names::part`] gives for a text are then the same in every such
    /// dictionary with the same `hash`, unless [`Names::collided`].
    pub fn canonical(hash: fn(&[u8]) -> u128) -> Self {
        Self {
            labels: Some(Labels {
                hash,
                of: Vec::new(),
                held: FxHashSet::default(),
                collided: false,
            }),
            ..Self::default()
        }
    }

    /// Whether a rule got its number as its label because another rule held its hash, so that
    /// the parse may depend on what the dictionary met before; always false in a dictionary
    /// made by [`Names::new`].
    pub fn collided(&self) -> bool {
        self.labels.as_ref().is_some_and(|l| l.collided)
    }

    /// What `n`, a name this dictionary gave, stands for. Only a dictionary made by
    /// [`Names::canonical`] gives them.
    pub fn part(&self, n: Name) -> Part {
        if n.0 == EMPTY {
            return Part::Empty;
        }
        let Some(i) = n.0.checked_sub(FIRST_RULE) else {
            return Part::Byte(n.0 as u8);
        };
        assert!(
            self.labels.is_some(),
            "only a canonical dictionary gives the parts of a name"
        );
        match self.rules[i as usize] {
            Rule::Run(sym, count) => Part::Run(Name(sym), count),
            Rule::Block(len, syms) => Part::Block(Parts {
                len,
                names: syms.map(Name),
            }),
        }
    }

    /// The canonical name of `t`: `O(n log N)` dictionary steps for a text of `n` nodes not named
    /// before and `N` bytes, each node's summary kept for the next text that shares it.
    pub fn name(&mut self, t: &Text) -> Name {
        Name(self.sum(t).map_or(EMPTY, |s| s.name))
    }

    /// The summary of `t`, none for the empty text: a block parsed whole, a node and a deep tree
    /// joined from their parts' summaries left to right. The recursion is as deep as the tree,
    /// at most 63 levels (text.rs).
    fn sum(&mut self, t: &Text) -> Option<Arc<Sum>> {
        let key = Arc::as_ptr(&t.0).addr();
        if let Some((_, s)) = self.memo.get(&key) {
            return s.clone();
        }
        let s = match &*t.0 {
            Tree::Empty => None,
            Tree::Block { block, .. } => self.leaf(block.as_bytes()),
            Tree::Node { parts, .. } => self.fold(parts.iter().flatten()),
            Tree::Deep {
                front,
                middle,
                back,
                ..
            } => self.fold(
                front
                    .iter()
                    .flatten()
                    .chain(std::iter::once(middle))
                    .chain(back.iter().flatten()),
            ),
        };
        self.memo.insert(key, (t.clone(), s.clone()));
        s
    }

    fn fold<'a>(&mut self, parts: impl Iterator<Item = &'a Text>) -> Option<Arc<Sum>> {
        let mut acc = None;
        for part in parts {
            let s = self.sum(part);
            acc = self.join(acc, s);
        }
        acc
    }

    /// The number of `rule`, a new one when the dictionary has not met it. A new rule of a
    /// canonical dictionary gets its label here, once: its hash, or its number when another
    /// rule holds that hash (the module's comment).
    fn rule(&mut self, rule: Rule) -> u64 {
        let rules = &self.rules;
        let place = match self.find.entry(
            FxBuildHasher.hash_one(rule),
            |&i| rules[i] == rule,
            |&i| FxBuildHasher.hash_one(rules[i]),
        ) {
            Entry::Occupied(e) => return FIRST_RULE + *e.get() as u64,
            Entry::Vacant(e) => {
                let place = rules.len();
                e.insert(place);
                place
            }
        };
        self.rules.push(rule);
        let n = FIRST_RULE + place as u64;
        if let Some(l) = &mut self.labels {
            let hashed = l.of_rule(&rule);
            let label = if l.held.insert(hashed) {
                hashed
            } else {
                l.collided = true;
                u128::from(n)
            };
            l.of.push(label);
        }
        n
    }

    /// [`decide`] for the symbols `ids`, reading as labels the numbers themselves in a
    /// dictionary made by [`Names::new`], the labels in a canonical one. Different symbols
    /// have different labels either way (the module's comment), and neighbors are different
    /// symbols, since a level is run-length coded.
    fn decide(&self, ids: &[u64], ts: bool, te: bool) -> Vec<bool> {
        match &self.labels {
            None => decide(ids.len(), |i| u128::from(ids[i]), ts, te),
            Some(l) => decide(ids.len(), |i| l.label(ids[i]), ts, te),
        }
    }

    /// The symbol a run-length entry stands for at its level.
    fn id(&mut self, e: Ent) -> u64 {
        if e.count == 1 {
            e.sym
        } else {
            self.rule(Rule::Run(e.sym, e.count))
        }
    }

    fn ids(&mut self, w: &[Ent]) -> Vec<u64> {
        w.iter().map(|&e| self.id(e)).collect()
    }

    fn block(&mut self, ids: &[u64]) -> u64 {
        let mut syms = [0; MAX_BLOCK];
        syms.get_mut(..ids.len())
            .expect("a block holds at most MAX_BLOCK symbols (the proof at MAX_BLOCK)")
            .copy_from_slice(ids);
        self.rule(Rule::Block(ids.len() as u8, syms))
    }

    /// The names of the blocks from the start `lo` to the start or end `hi`, and where each
    /// begins.
    fn blocks(&mut self, ids: &[u64], st: &[bool], lo: usize, hi: usize) -> (Vec<u64>, Vec<usize>) {
        // Room for blocks of 2 symbols each, as most are: it only saves growing the lists in
        // steps, and a list still grows past it when a window has more blocks.
        let room = (hi - lo) / 2 + 2;
        let (mut out, mut starts) = (Vec::with_capacity(room), Vec::with_capacity(room));
        let mut b = lo;
        for i in lo + 1..=hi {
            if i == hi || st[i] {
                out.push(self.block(&ids[b..i]));
                starts.push(b);
                b = i;
            }
        }
        (out, starts)
    }

    /// The summary of a nonempty block of bytes, none for an empty one: `O(b)` for `b` bytes.
    fn leaf(&mut self, data: &[u8]) -> Option<Arc<Sum>> {
        if data.is_empty() {
            return None;
        }
        let mut ents: Vec<Ent> = Vec::with_capacity(data.len());
        for &b in data {
            match ents.last_mut() {
                Some(e) if e.sym == u64::from(b) => e.count += 1,
                _ => ents.push(Ent {
                    sym: u64::from(b),
                    count: 1,
                }),
            }
        }
        Some(Arc::new(self.levels(vec![Some(Seg::Ents(ents))])))
    }

    /// The summary of `x` followed by `y`: `O(K)` dictionary steps at each level of the result.
    fn join(&mut self, x: Option<Arc<Sum>>, y: Option<Arc<Sum>>) -> Option<Arc<Sum>> {
        match (x, y) {
            (None, s) | (s, None) => s,
            (Some(x), Some(y)) => Some(Arc::new(self.levels(vec![seg_of(&x, 0), seg_of(&y, 0)]))),
        }
    }

    /// The levels of a text whose level 0 is the middle `segs`, with nothing before or after it.
    fn levels(&mut self, mut segs: Vec<Option<Seg>>) -> Sum {
        let (mut p, mut q) = (Vec::new(), Vec::new());
        let mut levels = Vec::new();
        loop {
            let s = norm(segs);
            let step = self.step(&p, &s, &q);
            let mid = store(&s);
            match step {
                Step::Name(name) => {
                    levels.push(Level {
                        mid,
                        lskip: None,
                        rskip: None,
                    });
                    return Sum { levels, name };
                }
                Step::Next {
                    lskip,
                    rskip,
                    p: p2,
                    segs: segs2,
                    q: q2,
                } => {
                    levels.push(Level { mid, lskip, rskip });
                    (p, segs, q) = (p2, segs2, q2);
                }
            }
        }
    }

    /// From one level of a text, the entries `p` before the middle `segs` and `q` after it, to
    /// the next, or to the text's name when the level is one symbol.
    fn step(&mut self, p: &[Ent], segs: &[Seg], q: &[Ent]) -> Step {
        let ops: Vec<usize> = (0..segs.len())
            .filter(|&i| matches!(segs[i], Seg::Mid(..)))
            .collect();
        let (Some(&first), Some(&last)) = (ops.first(), ops.last()) else {
            return self.step_whole(p, segs, q);
        };
        // A join has two parts, each with at most one long middle at a level.
        debug_assert!(ops.len() <= 2);
        let (Seg::Mid(s1, lv1), Seg::Mid(sn, lvn)) = (&segs[first], &segs[last]) else {
            unreachable!("ops holds the places of long middles")
        };
        let l1 = long(s1, *lv1);
        let ln = long(sn, *lvn);
        // The first gap: the true start to the first block start inside the first long middle.
        let head1 = &l1.head[..l1.lskip + CR];
        let mut parts: Vec<&[Ent]> = vec![p];
        parts.extend(segs[..first].iter().map(ents));
        parts.push(head1);
        let (w0, st0) = cat(&parts);
        let pos0 = st0[1];
        let hi0 = st0[st0.len() - 1] + l1.lskip;
        let ids0 = self.ids(&w0);
        let d0 = self.decide(&ids0, true, false);
        let (syms0, bs0) = self.blocks(&ids0, &d0, 0, hi0);
        let s = (pos0 + CL + 1..hi0).find(|&i| d0[i]).unwrap_or(hi0);
        let i_s = if s < hi0 {
            start_index(&bs0, s)
        } else {
            syms0.len()
        };
        // The last gap: the last block start inside the last long middle to the true end.
        let tailn = &ln.tail[ln.tail.len() - (ln.rskip + CL)..];
        let mut parts: Vec<&[Ent]> = vec![tailn];
        parts.extend(segs[last + 1..].iter().map(ents));
        let before_q = cat(&parts).0;
        parts.push(q);
        let (w2, _) = cat(&parts);
        let e_last = before_q.len() - 1;
        let ids2 = self.ids(&w2);
        let d2 = self.decide(&ids2, false, true);
        let (syms2, bs2) = self.blocks(&ids2, &d2, CL, w2.len());
        let t = (CL + 1..e_last.saturating_sub(CR))
            .rev()
            .find(|&i| d2[i])
            .unwrap_or(CL);
        let i_t = start_index(&bs2, t);
        let mut next = vec![Some(Seg::Ents(rle(&syms0[i_s..]))), seg_of(s1, lv1 + 1)];
        if first != last {
            // The gap between the two long middles.
            let tail1 = &l1.tail[l1.tail.len() - (l1.rskip + CL)..];
            let headn = &ln.head[..ln.lskip + CR];
            let mut parts: Vec<&[Ent]> = vec![tail1];
            parts.extend(segs[first + 1..last].iter().map(ents));
            parts.push(headn);
            let (w1, st1) = cat(&parts);
            let hi1 = st1[st1.len() - 1] + ln.lskip;
            let ids1 = self.ids(&w1);
            let d1 = self.decide(&ids1, false, false);
            let (mid, _) = self.blocks(&ids1, &d1, CL, hi1);
            next.push(Some(Seg::Ents(rle(&mid))));
            next.push(seg_of(sn, lvn + 1));
        }
        next.push(Some(Seg::Ents(rle(&syms2[..i_t]))));
        Step::Next {
            lskip: Some(s - pos0),
            rskip: Some(e_last + 1 - t),
            p: rle(&syms0[..i_s]),
            segs: next,
            q: rle(&syms2[i_t..]),
        }
    }

    /// [`Names::step`] for a level held whole: the window is parsed from end to end.
    fn step_whole(&mut self, p: &[Ent], segs: &[Seg], q: &[Ent]) -> Step {
        // `norm` joined neighboring entries, and no piece is a long middle here, so the middle
        // is at most one piece.
        let mid: &[Ent] = match segs {
            [] => &[],
            [s] => ents(s),
            _ => unreachable!("norm joins neighboring entries into one piece"),
        };
        let (w, st0) = cat(&[p, mid, q]);
        let ids = self.ids(&w);
        if let [name] = ids[..] {
            return Step::Name(name);
        }
        assert!(!ids.is_empty(), "a level of a nonempty text has a symbol");
        let st = self.decide(&ids, true, true);
        let (syms, bstart) = self.blocks(&ids, &st, 0, w.len());
        let whole = |syms: &[u64]| Step::Next {
            lskip: None,
            rskip: None,
            p: rle(syms),
            segs: Vec::new(),
            q: Vec::new(),
        };
        if mid.is_empty() {
            return whole(&syms);
        }
        let pos0 = st0[1];
        let e_last = pos0 + mid.len() - 1;
        let s = (pos0 + CL + 1..w.len()).find(|&i| st[i]);
        let t = s.and_then(|s| (s + 1..e_last.saturating_sub(CR)).rev().find(|&i| st[i]));
        let (Some(s), Some(t)) = (s, t) else {
            return whole(&syms);
        };
        let (i_s, i_t) = (start_index(&bstart, s), start_index(&bstart, t));
        Step::Next {
            lskip: Some(s - pos0),
            rskip: Some(e_last + 1 - t),
            p: rle(&syms[..i_s]),
            segs: vec![Some(Seg::Ents(rle(&syms[i_s..i_t])))],
            q: rle(&syms[i_t..]),
        }
    }
}

/// The place of the block that starts at `s` among the starts `starts`, which hold it.
fn start_index(starts: &[usize], s: usize) -> usize {
    starts
        .binary_search(&s)
        .expect("the parse has a block start at s, found in the parse")
}

/// The entries of a piece that is entries; a long middle is never read whole.
fn ents(s: &Seg) -> &[Ent] {
    match s {
        Seg::Ents(e) => e,
        Seg::Mid(..) => unreachable!("a long middle stands between the windows, never in one"),
    }
}

/// The long middle of `s`'s level `lv`, with its skips.
fn long(s: &Sum, lv: usize) -> Long<'_> {
    let level = &s.levels[lv];
    let Some(Mid::Long { head, tail, count }) = &level.mid else {
        unreachable!("a Seg::Mid points at a long middle")
    };
    Long {
        head,
        tail,
        count: *count,
        lskip: level
            .lskip
            .expect("a long middle has a block start inside it"),
        rskip: level
            .rskip
            .expect("a long middle has a block start inside it"),
    }
}

/// Level `lv` of `s`'s middle as a piece: none, its entries, or a reference to it when long.
fn seg_of(s: &Arc<Sum>, lv: usize) -> Option<Seg> {
    match &s.levels[lv].mid {
        None => None,
        Some(Mid::Full(e)) => Some(Seg::Ents(e.clone())),
        Some(Mid::Long { .. }) => Some(Seg::Mid(Arc::clone(s), lv)),
    }
}

fn first_entry(s: &Seg) -> Ent {
    match s {
        Seg::Ents(e) => e[0],
        Seg::Mid(sum, lv) => long(sum, *lv).head[0],
    }
}

fn last_entry(s: &Seg) -> Ent {
    match s {
        Seg::Ents(e) => e[e.len() - 1],
        Seg::Mid(sum, lv) => {
            let tail = long(sum, *lv).tail;
            tail[tail.len() - 1]
        }
    }
}

/// The pieces without the missing and empty ones, neighboring entries joined.
fn norm(segs: Vec<Option<Seg>>) -> Vec<Seg> {
    let mut out: Vec<Seg> = Vec::new();
    for s in segs.into_iter().flatten() {
        match (s, out.last_mut()) {
            (Seg::Ents(e), _) if e.is_empty() => {}
            (Seg::Ents(e), Some(Seg::Ents(prev))) => *prev = cat(&[prev, &e]).0,
            (s, _) => out.push(s),
        }
    }
    out
}

/// The kept form of a middle given as pieces.
fn store(segs: &[Seg]) -> Option<Mid> {
    if segs.is_empty() {
        return None;
    }
    let mut count = 0;
    for (i, s) in segs.iter().enumerate() {
        count += match s {
            Seg::Ents(e) => e.len(),
            Seg::Mid(sum, lv) => long(sum, *lv).count,
        };
        if i > 0 && last_entry(&segs[i - 1]).sym == first_entry(s).sym {
            count -= 1;
        }
    }
    if let [Seg::Ents(e)] = segs {
        return Some(if count <= 2 * K {
            Mid::Full(e.clone())
        } else {
            Mid::Long {
                head: e[..K].to_vec(),
                tail: e[e.len() - K..].to_vec(),
                count,
            }
        });
    }
    // Two pieces of entries are never neighbors (`norm`), so a list of pieces that is not one
    // piece of entries holds a long middle, whose ends give the ends of the whole.
    let mut hp: Vec<&[Ent]> = Vec::new();
    for s in segs {
        match s {
            Seg::Ents(e) => hp.push(e),
            Seg::Mid(sum, lv) => {
                hp.push(long(sum, *lv).head);
                break;
            }
        }
    }
    let mut tp: Vec<&[Ent]> = Vec::new();
    for s in segs.iter().rev() {
        match s {
            Seg::Ents(e) => tp.push(e),
            Seg::Mid(sum, lv) => {
                tp.push(long(sum, *lv).tail);
                break;
            }
        }
    }
    tp.reverse();
    let mut head = cat(&hp).0;
    let tail = cat(&tp).0;
    assert!(head.len() >= K && tail.len() >= K && count > 2 * K);
    head.truncate(K);
    Some(Mid::Long {
        head,
        tail: tail[tail.len() - K..].to_vec(),
        count,
    })
}

/// The run-length entries of `syms`.
fn rle(syms: &[u64]) -> Vec<Ent> {
    let mut out: Vec<Ent> = Vec::with_capacity(syms.len());
    for &sym in syms {
        match out.last_mut() {
            Some(e) if e.sym == sym => e.count += 1,
            _ => out.push(Ent { sym, count: 1 }),
        }
    }
    out
}

/// The entries of `parts` in order, a part's first entry joined to the entry before it when the
/// two have one symbol, and the place of each part's first entry (of where it would be, for an
/// empty part).
fn cat(parts: &[&[Ent]]) -> (Vec<Ent>, Vec<usize>) {
    let mut out: Vec<Ent> = Vec::with_capacity(parts.iter().map(|p| p.len()).sum());
    let mut starts = Vec::with_capacity(parts.len());
    for p in parts {
        let at = out.len();
        match (p.split_first(), out.last_mut()) {
            (Some((f, rest)), Some(l)) if l.sym == f.sym => {
                starts.push(at - 1);
                l.count += f.count;
                out.extend_from_slice(rest);
            }
            _ => {
                starts.push(at);
                out.extend_from_slice(p);
            }
        }
    }
    (out, starts)
}

/// Where blocks start among `n` positions whose labels `label` gives, no two neighbors equal:
/// exact at `i` when `i ≥ 8` or `ts` (the window starts at the true start) and `i + 4 < n` or
/// `te` (it ends at the true end).
// Complexity tradeoff: four rounds each built a new list of 128-bit labels, 64 bytes a position
// in all, and the labels were first copied into a list of their own: for a flat string of L
// bytes, 80 L bytes allocated at level 0 alone (row PERF-canon-flat-strings). Here the first
// round reads the labels in place and writes one byte a position, and the later rounds rewrite
// those bytes in place: O(n) time as before, n bytes and n flags allocated. The labels and the
// starts are the same, so no address changed.
fn decide(n: usize, label: impl Fn(usize) -> u128, ts: bool, te: bool) -> Vec<bool> {
    // Four rounds of coin tossing: labels below 2^128, then 2^8, 16, 8 and 6 (a label below
    // 2^b differs from its neighbor first at a bit p < b, and becomes 2p + bit p < 2b). A
    // number below 2^64, widened, gives the same first differing bit and the same bit there,
    // so a dictionary made by `Names::new` parses exactly as when its numbers were read as
    // u64: below 2^64, then 2^7, 14, 8 and 6. After the first round a label is below 2^8, so
    // a byte holds it.
    let toss = |x: u128, left: Option<u128>| -> u8 {
        let p = left.map_or(0, |l| {
            debug_assert!(x != l, "neighbors' labels differ");
            (x ^ l).trailing_zeros()
        });
        (2 * p + ((x >> p) & 1) as u32) as u8
    };
    let mut lab: Vec<u8> = Vec::with_capacity(n);
    let mut left = None;
    for i in 0..n {
        let x = label(i);
        lab.push(toss(x, left));
        left = Some(x);
    }
    // The other three rounds in place, from the right, so that the left neighbor still holds
    // the last round's label when a position is tossed.
    for _ in 1..4 {
        for i in (0..n).rev() {
            let l = i.checked_sub(1).map(|j| u128::from(lab[j]));
            lab[i] = toss(u128::from(lab[i]), l);
        }
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

#[cfg(test)]
mod tests;

#[cfg(test)]
mod bench;
