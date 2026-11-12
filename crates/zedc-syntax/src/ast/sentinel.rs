//! The entries each sentinel site of a loop body gives, by the values of their keys, and the
//! check that no two sites give one entry (DESIGN.md sec:generations, row "Two sentinel values
//! for one variable"). `initial x = e;` and `mutable x = e;` give the entry `x[-1]`;
//! `initial x[-2] = e;` gives `x[-2]`; `initial x[i in -3..<0] = e;` gives `x[-3]`, `x[-2]`
//! and `x[-1]`; and a further bracket, `initial g[-1][j in 0..<2] = j;`, gives entries inside
//! the frame `g[-1]`, which a site that gives the whole frame `g[-1]` gives too. Keys written
//! as integer literals are compared by value, so `x[-2]`, `x[- 2]`, `x[-0x2]` and
//! `x[i in -2..=-2]` are one entry, and a run of keys collides with every site whose keys
//! meet it.

use std::collections::HashMap;

use num_bigint::BigInt;

use super::{Expr, ExprKind, IndexKey, RangeEnd};

/// The last key of a run of keys, or `Above` for `lo..`, which has none.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) enum End {
    At(BigInt),
    Above,
}

impl End {
    /// Whether the run ending here reaches the key `lo`.
    pub(super) fn reaches(&self, lo: &BigInt) -> bool {
        match self {
            End::At(h) => h >= lo,
            End::Above => true,
        }
    }
}

/// The keys one bracket of an entry gives: the integers from the first to the end, when the
/// text writes them as integer literals; otherwise the key as built, shown as an
/// s-expression, which only the same key equals.
#[derive(Debug, PartialEq, Eq, Hash)]
pub(super) enum Keys {
    Ints(BigInt, End),
    Written(String),
}

/// The value of `e` when it is an integer literal, `2`, `0x2`, or one negated, `-2`.
pub(super) fn int_literal(e: &Expr) -> Option<BigInt> {
    let (negated, e) = match &e.kind {
        ExprKind::Unary("-", x) => (true, &**x),
        _ => (false, e),
    };
    let ExprKind::Int { radix, digits } = &e.kind else {
        return None;
    };
    let v = BigInt::parse_bytes(digits.as_bytes(), *radix)?;
    Some(if negated { -v } else { v })
}

/// The keys of the bracket `k`; none when it is a range written with integer literals that
/// holds no key, `i in -1..<-1`.
pub(super) fn keys_of(k: &IndexKey) -> Option<Keys> {
    let written = |e: &Expr, prefix: &str| Some(Keys::Written(format!("{prefix}{e}")));
    match k {
        IndexKey::At(e) => match int_literal(e) {
            Some(v) => Some(Keys::Ints(v.clone(), End::At(v))),
            None => written(e, ""),
        },
        IndexKey::In { set, .. } => {
            let ExprKind::Range(lo, end) = &set.kind else {
                return written(set, "in ");
            };
            let Some(lo) = int_literal(lo) else {
                return written(set, "in ");
            };
            let end = match end {
                RangeEnd::Below(b) => match int_literal(b) {
                    Some(b) => End::At(b - 1),
                    None => return written(set, "in "),
                },
                RangeEnd::Through(b) => match int_literal(b) {
                    Some(b) => End::At(b),
                    None => return written(set, "in "),
                },
                RangeEnd::Open => End::Above,
            };
            end.reaches(&lo).then_some(Keys::Ints(lo, end))
        }
    }
}

/// The entries one site gives one variable: the variable; the generation keys, `lo` to `end`,
/// on the line of keys `line`, which is `None` for integer keys and the generation key as
/// built for a key the text does not fix (that line holds the one key `0..=0`); the keys of
/// the later brackets, none for whole frames; and the index of the statement in the body.
pub(super) struct Entry<'s> {
    pub name: &'s str,
    pub line: Option<String>,
    pub lo: BigInt,
    pub end: End,
    pub inner: Vec<Keys>,
    pub stmt: usize,
}

/// The sites of one class inserted so far: a Fenwick tree over their first keys, in order,
/// whose node holds the site with the latest end among the starts it covers. A run `lo` to
/// `end` meets a site of the class exactly when the latest end among the sites starting at or
/// below `end` reaches `lo`.
struct Class {
    /// The sites the class will hold, by first key, one for each distinct key.
    starts: Vec<usize>,
    tree: Vec<Option<usize>>,
}

/// Whether site `i` ends later than site `j`, the earlier written winning a tie.
fn later(entries: &[Entry], i: usize, j: Option<usize>) -> bool {
    j.is_none_or(|j| entries[i].end > entries[j].end || entries[i].end == entries[j].end && i < j)
}

impl Class {
    fn insert(&mut self, entries: &[Entry], i: usize) {
        let mut r = self
            .starts
            .partition_point(|&j| entries[j].lo < entries[i].lo)
            + 1;
        while r <= self.tree.len() {
            if later(entries, i, self.tree[r - 1]) {
                self.tree[r - 1] = Some(i);
            }
            r += r.isolate_lowest_one();
        }
    }

    /// A site of the class that meets the run of site `i`, the latest ending.
    fn meets(&self, entries: &[Entry], i: usize) -> Option<usize> {
        let mut r = match &entries[i].end {
            End::At(h) => self.starts.partition_point(|&j| entries[j].lo <= *h),
            End::Above => self.starts.len(),
        };
        let mut best = None;
        while r > 0 {
            if let Some(j) = self.tree[r - 1]
                && later(entries, j, best)
            {
                best = Some(j);
            }
            r &= r - 1;
        }
        best.filter(|&j| entries[j].end.reaches(&entries[i].lo))
    }
}

/// The sites of a loop body, checked in written order: each against the sites before it that
/// can give the same entry. Sites of one variable and one line fall in three classes: those
/// that give whole frames, those whose later brackets have one value (one class for each),
/// and all those with later brackets. A site that gives whole frames meets a site of the first
/// or the third class whose generation keys meet its own; a site with later brackets meets one
/// of the first class, or of its own class of the second, likewise.
// Complexity tradeoff: the naive check compares each site with every site before it, O(k^2)
// for k sites; each class here is a Fenwick tree over the first keys of its sites, so each
// site is one query and one insertion in O(log k), O(k log k) in all, with the keys compared
// by value (num-bigint, so a key of any width). Given up: two sites whose later brackets
// differ by value but meet, `g[-1][j in 0..<2]` beside `g[-1][1]`, are not caught here (a
// check over boxes in more dimensions needs a range tree, O(k log^(d-1) k)); nor are keys the
// text does not fix as integers, `x[i in -k..<0]` beside `x[-1]`, which only the same key
// built the same way meets. Both are caught by the boundary analysis of step L6.8a (range
// analysis of the keys); the tests are `two_sentinel_values_for_one_variable_are_refused`
// and `overlapping_entries_scale` in tests/steps/l06_01_parser/initial.rs, COMPLEXITY.md row
// "Two sentinel values: entries by value".
pub(super) struct Sentinels<'s> {
    entries: Vec<Entry<'s>>,
    classes: Vec<Class>,
    /// For each site, the classes it is inserted into and the classes it is checked against.
    homes: Vec<[Option<usize>; 2]>,
    asks: Vec<[usize; 2]>,
}

impl<'s> Sentinels<'s> {
    /// The checker of the sites `entries`, in written order.
    pub(super) fn new(entries: Vec<Entry<'s>>) -> Self {
        let mut lines: HashMap<(&str, Option<&str>), usize> = HashMap::new();
        let mut forms: HashMap<(usize, &[Keys]), usize> = HashMap::new();
        let mut members: Vec<Vec<usize>> = Vec::new();
        let mut homes = Vec::with_capacity(entries.len());
        let mut asks = Vec::with_capacity(entries.len());
        for (i, e) in entries.iter().enumerate() {
            let next = members.len();
            let line = *lines.entry((e.name, e.line.as_deref())).or_insert_with(|| {
                members.extend([Vec::new(), Vec::new()]);
                next
            });
            let (whole, any) = (line, line + 1);
            if e.inner.is_empty() {
                homes.push([Some(whole), None]);
                asks.push([whole, any]);
            } else {
                let next = members.len();
                let form = *forms.entry((line, &e.inner[..])).or_insert_with(|| {
                    members.push(Vec::new());
                    next
                });
                homes.push([Some(form), Some(any)]);
                asks.push([whole, form]);
            }
            for c in homes[i].into_iter().flatten() {
                members[c].push(i);
            }
        }
        let classes = members
            .into_iter()
            .map(|mut starts| {
                starts.sort_by(|&a, &b| entries[a].lo.cmp(&entries[b].lo));
                starts.dedup_by(|a, b| entries[*a].lo == entries[*b].lo);
                let tree = vec![None; starts.len()];
                Class { starts, tree }
            })
            .collect();
        Sentinels {
            entries,
            classes,
            homes,
            asks,
        }
    }

    pub(super) fn entries(&self) -> &[Entry<'s>] {
        &self.entries
    }

    /// Checks site `i` against the sites before it, which must all have been checked, and
    /// adds it: a site before it that gives an entry it gives, if any, the one written first
    /// among the latest ending of each class it is checked against.
    pub(super) fn check(&mut self, i: usize) -> Option<usize> {
        let Sentinels {
            entries,
            classes,
            homes,
            asks,
        } = self;
        let met = asks[i]
            .iter()
            .filter_map(|&c| classes[c].meets(entries, i))
            .min();
        for c in homes[i].into_iter().flatten() {
            classes[c].insert(entries, i);
        }
        met
    }
}
