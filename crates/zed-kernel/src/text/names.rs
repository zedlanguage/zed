//! Canonical names of texts: one number per text, the same for equal texts and different for
//! different ones, shared by every text named through one [`Names`] (item STAGE-joined-eq-build;
//! docs/joined-strings-study.md). Staging keys its tables by these names, so that two calls at
//! equal joined strings are found equal without reading the strings.
//!
//! The method is the signature encoding of Mehlhorn, Sundar and Uhrig ("Maintaining dynamic
//! sequences under equality tests in polylogarithmic time", Algorithmica 17(2):183-198, 1997,
//! doi:10.1007/BF02522825), with the block rule of Alstrup, Brodal and Rauhe ("Pattern
//! matching in dynamic texts", SODA 2000, pp. 819-828; not in Crossref). The blocks use the
//! deterministic coin tossing of R. Cole and U. Vishkin ("Deterministic coin tossing with
//! applications to optimal parallel list ranking", Information and Control 70(1):32-53, 1986,
//! doi:10.1016/S0019-9958(86)80023-7): a position whose label differs from its left
//! neighbor's in lowest bit `p` takes the new label `2p + (its bit p)`, so neighbors stay
//! different and a label of `b` bits becomes one of about `log b` bits. Crossref checked
//! 2026-11-20 for the two DOIs; none of the three texts was obtained, so the methods are from
//! memory, as are the SODA pages. Departure: the papers keep the encoding under updates of a
//! dynamic sequence; here texts are only named and joined, and the constants are this file's.
//! Related, and named beside these in COMPLEXITY.md: T. Nishimoto, T. I, S. Inenaga, H. Bannai
//! and M. Takeda, "Fully dynamic data structure for LCE queries in compressed space", MFCS
//! 2016, LIPIcs 58, doi:10.4230/LIPIcs.MFCS.2016.72 (DataCite checked 2026-11-20, text not
//! read), which builds the signature encoding from a straight-line program; nothing here is
//! taken from it.
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
//! only whether the join of two summaries (`Names::join`) gives the name of the whole text,
//! and the tests check it against byte comparison.
//!
//! Locality: whether a block starts at position `i` reads only the symbols `i − 8 ..= i + 4`
//! (four rounds read one left neighbor each, the three passes one on each side, and a maximum
//! one more on each side). Position 0 tosses with `p = 0`, and its label still differs from
//! position 1's: position 1 differs from position 0 in bit `p ≥ 0`, and if `p = 0` the two
//! labels differ in their low bit, else in the bits above it. At a true start the parse puts a
//! start at position 0 and none at 1; at a true end, none at the last position.
//!
//! The parse reads the numbers the dictionary gave, so the blocks of a text, though not its
//! being equal to another, depend on what the dictionary met before. (A dictionary whose
//! parse read content labels in place of the numbers, so that the blocks were the text's
//! alone, wrote strings into content addresses from item CANON-term-string-nodes until the
//! author chose to write a string's bytes there, answer A106, 2026-11-20; it was removed
//! with that use.)
//!
//! A text is held as a summary (`Sum`): at each level, the part of the sequence that does not
//! depend on what is joined to either side (the middle), as run-length entries, kept whole when
//! short and as its first and last `K` entries when long, and the number of entries between
//! the middle and the true parse's next block start on each side (the skips). The join of two
//! summaries parses again, at each level, only the windows where an end meets the middle.

use hashbrown::HashTable;
use hashbrown::hash_table::Entry;
use std::hash::BuildHasher;
use std::sync::Arc;

use super::tree::{Text, Tree};
use crate::digest::{DigestMap, TextState};

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
// The tables do not hash with the standard SipHash, which was a fifth of the work of a flat
// string (row PERF-canon-flat-strings; SipHash: Aumasson and Bernstein 2012,
// doi:10.1007/978-3-642-34931-7_28, full comment in `digest.rs`, type `FixedState`). The memo
// of nodes is keyed by addresses, so it takes the unseeded `Digest`. A rule of level 0 is a
// block of the text's own bytes, which a program chooses, so the table of rules takes the
// seeded `TextState`, one seed per dictionary (it was FxHash, with no seed, which let a text
// choose blocks that share a slot; DRY-sorted-structures-2 job 3). A rule's number is the
// count of rules met before it, read from no hash, so no seed reaches a name. Each rule is
// kept once, in `rules`,
// and the table that finds it holds its place there, a word, where a map from rules to numbers
// held the rule again in each 64-byte slot.
#[derive(Default)]
pub struct Names {
    /// The rule of each number from [`FIRST_RULE`] on, in order.
    rules: Vec<Rule>,
    /// The places in `rules`, found by the hash of the rule by `text`.
    find: HashTable<usize>,
    /// The hasher of `find`, seeded at random for each dictionary.
    text: TextState,
    // The address of a node's tree, kept alive by the `Text` beside it, names the node for
    // identity only, never for order.
    memo: DigestMap<usize, (Text, Option<Arc<Sum>>)>,
}

impl std::fmt::Debug for Names {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Names")
            .field("rules", &self.rules.len())
            .field("nodes", &self.memo.len())
            .finish()
    }
}

impl Names {
    /// An empty dictionary.
    pub fn new() -> Self {
        Self::default()
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

    /// The number of `rule`, a new one when the dictionary has not met it.
    fn rule(&mut self, rule: Rule) -> u64 {
        let (rules, text) = (&self.rules, &self.text);
        let place = match self.find.entry(
            text.hash_one(rule),
            |&i| rules[i] == rule,
            |&i| text.hash_one(rules[i]),
        ) {
            Entry::Occupied(e) => return FIRST_RULE + *e.get() as u64,
            Entry::Vacant(e) => {
                let place = rules.len();
                e.insert(place);
                place
            }
        };
        self.rules.push(rule);
        FIRST_RULE + place as u64
    }

    /// Room for `more` new rules in each table that holds one entry per rule.
    fn reserve(&mut self, more: usize) {
        let (rules, text) = (&self.rules, &self.text);
        self.find.reserve(more, |&i| text.hash_one(rules[i]));
        self.rules.reserve(more);
    }

    /// [`decide`] for the symbols `ids`, reading as labels the numbers themselves. Different
    /// symbols have different numbers, and neighbors are different symbols, since a level is
    /// run-length coded.
    // Proof of the two claims, which `decide`'s labels need (its debug check that neighbors'
    // labels differ). (1) Different symbols have different numbers: a byte is its own number,
    // below `FIRST_RULE`; a rule's number is `FIRST_RULE + place`, `place` its index in
    // `rules`, and `rule` gives a rule met before its old place (the `find` table matches by
    // `rules[i] == rule`) and a new rule a new place, so equal rules share a number and
    // different rules have different ones. (2) Neighbors in `ids` differ. Every caller passes
    // `self.ids(w)` (`step`, `step_whole`) or ids made from `byte_runs` (`leaf`), where `w` is
    // run-length coded: made by `rle` or `byte_runs`, each of which joins equal neighbors, or
    // by `cat` of such lists, which joins the two entries at each boundary when their symbols
    // are equal, or held from such a list (`norm`, `long`). So neighbors `e`, `f` in `w` have
    // `e.sym != f.sym`. A symbol at level 0 is a byte, and at a higher level the number of a
    // `Rule::Block` (`blocks` names each block by `block`, which makes a `Block` even for one
    // symbol), so no symbol is the number of a `Rule::Run`. `id` gives `e.sym` itself for a
    // count of 1 and the number of `Run(e.sym, e.count)` otherwise. Both of count 1: the
    // numbers are `e.sym != f.sym`. One of count 1: one number is a byte or a `Block`'s, the
    // other a `Run`'s, a different rule, so by (1) they differ. Both above 1: `Run(e.sym, _)`
    // and `Run(f.sym, _)` are different rules, so by (1) their numbers differ. The labels are
    // the numbers widened to `u128`, which keeps them different.
    fn decide(&self, ids: &[u64], ts: bool, te: bool) -> Vec<bool> {
        decide(ids.len(), |i| u128::from(ids[i]), ts, te)
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
        self.reserve(data.len() / 2);
        let ids: Vec<u64> = byte_runs(data).map(|e| self.id(e)).collect();
        let m = ids.len();
        let mid = if m <= 2 * K {
            Mid::Full(byte_runs(data).collect())
        } else {
            let mut tail: Vec<Ent> = byte_runs_back(data).take(K).collect();
            tail.reverse();
            Mid::Long {
                head: byte_runs(data).take(K).collect(),
                tail,
                count: m,
            }
        };
        let step = self.step_ids(&ids, 0, m);
        Some(Arc::new(self.climb(Some(mid), step)))
    }

    /// The summary of `x` followed by `y`: `O(K)` dictionary steps at each level of the result.
    fn join(&mut self, x: Option<Arc<Sum>>, y: Option<Arc<Sum>>) -> Option<Arc<Sum>> {
        match (x, y) {
            (None, s) | (s, None) => s,
            (Some(x), Some(y)) => Some(Arc::new(self.levels(vec![seg_of(&x, 0), seg_of(&y, 0)]))),
        }
    }

    /// The levels of a text whose level 0 is the middle `segs`, with nothing before or after it.
    fn levels(&mut self, segs: Vec<Option<Seg>>) -> Sum {
        let s = norm(segs);
        let step = self.step(&[], &s, &[]);
        self.climb(store(&s), step)
    }

    /// The levels of a text from one whose middle is `mid` and whose parse gave `step`.
    fn climb(&mut self, mut mid: Option<Mid>, mut step: Step) -> Sum {
        let mut levels = Vec::new();
        loop {
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
                    p,
                    segs,
                    q,
                } => {
                    levels.push(Level { mid, lskip, rskip });
                    let s = norm(segs);
                    step = self.step(&p, &s, &q);
                    mid = store(&s);
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
        // A middle with nothing on either side is read in place, not copied.
        let (ids, pos0) = if p.is_empty() && q.is_empty() {
            (self.ids(mid), 0)
        } else {
            let (w, st0) = cat(&[p, mid, q]);
            (self.ids(&w), st0[1])
        };
        self.step_ids(&ids, pos0, mid.len())
    }

    /// [`Names::step_whole`] for the symbols `ids` of a level held whole, whose middle is the
    /// `mid_len` entries from `pos0` on.
    fn step_ids(&mut self, ids: &[u64], pos0: usize, mid_len: usize) -> Step {
        if let [name] = ids[..] {
            return Step::Name(name);
        }
        assert!(!ids.is_empty(), "a level of a nonempty text has a symbol");
        let st = self.decide(ids, true, true);
        let (syms, bstart) = self.blocks(ids, &st, 0, ids.len());
        let whole = |syms: &[u64]| Step::Next {
            lskip: None,
            rskip: None,
            p: rle(syms),
            segs: Vec::new(),
            q: Vec::new(),
        };
        if mid_len == 0 {
            return whole(&syms);
        }
        let e_last = pos0 + mid_len - 1;
        let s = (pos0 + CL + 1..ids.len()).find(|&i| st[i]);
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

/// The run-length entries of the bytes `data`, from the first.
fn byte_runs(data: &[u8]) -> impl Iterator<Item = Ent> + '_ {
    data.chunk_by(|a, b| a == b).map(|r| Ent {
        sym: u64::from(r[0]),
        count: r.len() as u64,
    })
}

/// The run-length entries of the bytes `data`, from the last.
fn byte_runs_back(data: &[u8]) -> impl Iterator<Item = Ent> + '_ {
    data.chunk_by(|a, b| a == b).rev().map(|r| Ent {
        sym: u64::from(r[0]),
        count: r.len() as u64,
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
//
// The four rounds then ran as four passes over the list, each tossing through an `Option`, and
// the three passes and the maxima as four more, each finding its value through an iterator:
// about 125 instructions a position, a fifth of a flat string's address (row
// PERF-canon-flat-strings, the second time). Here one pass from the left runs all four rounds,
// keeping the left neighbor's label of each round in a register, and one pass runs the three
// passes and the maxima, each a few positions behind the one before (below). The values are the
// same, so no address changed; the test `decide_gives_the_starts_of_the_plain_rounds` checks
// this one against the plain rounds.
fn decide(n: usize, label: impl Fn(usize) -> u128, ts: bool, te: bool) -> Vec<bool> {
    // Four rounds of coin tossing: labels below 2^128, then 2^8, 16, 8 and 6 (a label below
    // 2^b differs from its neighbor first at a bit p < b, and becomes 2p + bit p < 2b). A
    // number below 2^64, widened, gives the same first differing bit and the same bit there,
    // so a dictionary made by `Names::new` parses exactly as when its numbers were read as
    // u64: below 2^64, then 2^7, 14, 8 and 6. After the first round a label is below 2^8, so
    // a byte holds it. Position 0 has no left neighbor and tosses with p = 0: its low bit.
    let toss = |x: u8, l: u8| -> u8 {
        debug_assert!(x != l, "neighbors' labels differ");
        let p = (x ^ l).trailing_zeros();
        (2 * p) as u8 + ((x >> p) & 1)
    };
    let mut lab: Vec<u8> = Vec::with_capacity(n);
    if n > 0 {
        let mut x = label(0);
        let first = (x & 1) as u8;
        lab.push(first);
        // The labels of position i − 1 after rounds 1, 2 and 3: round r + 1 at i tosses round
        // r's label at i against round r's at i − 1.
        let (mut l1, mut l2, mut l3) = (first, first, first);
        for i in 1..n {
            let y = label(i);
            debug_assert!(x != y, "neighbors' labels differ");
            let p = (x ^ y).trailing_zeros();
            let r1 = (2 * p) as u8 + ((y >> p) & 1) as u8;
            let r2 = toss(r1, l1);
            let r3 = toss(r2, l2);
            lab.push(toss(r3, l3));
            (x, l1, l2, l3) = (y, r1, r2, r3);
        }
    }
    // The three passes, for c = 5, 4, 3, each giving a position labeled c the least of 0, 1, 2
    // that neither neighbor holds, reading the left neighbor after this pass and the right one
    // before it. Pass c at position i reads pass c + 1 at i + 1, so in place, at step j, pass 5
    // runs at j, then pass 4 at j − 1, then pass 3 at j − 2: each reads at i − 1 its own
    // pass's value (written at the step before, and not yet overwritten, since the later pass
    // runs after it at each step) and at i + 1 the value the pass before wrote this step. The
    // maxima at j − 3 then read three values pass 3 has written. `NONE` stands for a missing
    // neighbor: no label equals it, and a maximum needs no neighbor's label below it.
    const NONE: u8 = u8::MAX;
    let at = |lab: &[u8], i: usize| -> u8 { lab.get(i).copied().unwrap_or(NONE) };
    let fix = |lab: &mut [u8], i: usize, c: u8| {
        if lab[i] == c {
            let left = i.checked_sub(1).map_or(NONE, |j| lab[j]);
            let right = at(lab, i + 1);
            lab[i] = if left != 0 && right != 0 {
                0
            } else if left != 1 && right != 1 {
                1
            } else {
                2
            };
        }
    };
    let mut st: Vec<bool> = Vec::with_capacity(n);
    let run = |lab: &mut [u8], st: &mut Vec<bool>, j: usize| {
        for (lag, c) in [(0, 5), (1, 4), (2, 3)] {
            if let Some(i) = j.checked_sub(lag).filter(|&i| i < n) {
                fix(lab, i, c);
            }
        }
        if let Some(i) = j.checked_sub(3).filter(|&i| i < n) {
            let left = i.checked_sub(1).map_or(NONE, |k| lab[k]);
            let right = at(lab, i + 1);
            st.push((left == NONE || lab[i] > left) && (right == NONE || lab[i] > right));
        }
    };
    // The steps whose positions all have both neighbors, 4 ≤ j < n − 1, without the checks.
    let inner = 4..n.saturating_sub(1).max(4);
    for j in 0..inner.start.min(n + 3) {
        run(&mut lab, &mut st, j);
    }
    for j in inner.clone() {
        for (i, c) in [(j, 5), (j - 1, 4), (j - 2, 3)] {
            if lab[i] == c {
                let (l, r) = (lab[i - 1], lab[i + 1]);
                lab[i] = if l != 0 && r != 0 {
                    0
                } else if l != 1 && r != 1 {
                    1
                } else {
                    2
                };
            }
        }
        let i = j - 3;
        st.push(lab[i] > lab[i - 1] && lab[i] > lab[i + 1]);
    }
    for j in inner.end.max(inner.start.min(n + 3))..n + 3 {
        run(&mut lab, &mut st, j);
    }
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
