//! Value words and the counted heap (step L1.36).
//!
//! **Words.** Native code passes every value as a [`Word`], a pair of 64-bit integers: a tag
//! and its payload. An integer in 64 bits, a float (its bits) and a boolean are unboxed, so
//! the arithmetic on them runs inline; a primitive as a function, a lookup port and a port's
//! state are unboxed too. Every other value is a cell of the heap, counted, or an entry of
//! the heap's table of uncounted values: a constant, the empty tuple and a bare atom, which
//! the memory plan of step L1.34 never counts either.
//!
//! **Cells.** The heap mirrors the cells of step L1.34 one for one, so a native run makes the
//! same allocations and count writes as the counting machine: a non-empty tuple and an atom
//! with a payload are a cell whose parts are words, a closure a cell holding its captures, a
//! string a cell holding its [`Text`], and a big integer, a rational, a keypath and a family a
//! cell holding the kernel value. A cell's count is the number of references to it; at 0 it
//! is freed, its parts dropped, and the next allocation takes it again. A cell's word carries
//! the cell's generation, which each free advances, so a use of a word after its cell was
//! freed is an error even when the cell holds another value by then.
//!
//! **The table.** An uncounted value is never freed, since no count says when its last word
//! goes. So the table grows only with what a run reads, never with how often: the empty tuple
//! and each bare atom have one entry, and the parts of an entry are entered once, together,
//! the first time a match reads them, so matching a constant again adds nothing (COMPLEXITY.md
//! R3, R6).

use std::collections::{BTreeMap, HashMap};
use std::ops::Deref;
use std::sync::Arc;
use std::{mem, slice};

use zed_kernel::paths::{Kept, Paths};
use zed_kernel::term::Pattern;
use zed_kernel::types::{Type, Universe};
use zed_kernel::value::{Atom, Fields, Items, SharedParts, Value};

use zed_kernel::Text;

/// A value as native code holds it: a tag and its payload.
#[repr(C)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Word {
    /// What the payload is: one of the tag constants.
    pub tag: i64,
    /// The payload.
    pub bits: i64,
}

impl Word {
    /// An integer in 64 bits; the payload is the integer.
    pub const INT: i64 = 0;
    /// A float; the payload is its bits, a NaN always the one canonical NaN.
    pub const FLOAT: i64 = 1;
    /// A boolean; the payload is 0 or 1.
    pub const BOOL: i64 = 2;
    /// A heap cell; the payload is its index, and its generation in the bits above
    /// [`INDEX_BITS`].
    pub const CELL: i64 = 3;
    /// An uncounted value; the payload is its index in the heap's table.
    pub const VAL: i64 = 4;
    /// A primitive as a function; the payload is its index in the program's table.
    pub const PRIM: i64 = 5;
    /// A lookup port; the payload is its index in the program's table.
    pub const SOURCE: i64 = 6;
    /// A port's state, which carries nothing.
    pub const STATE: i64 = 7;
    /// An error: the run stops, and the runtime holds the message.
    pub const ERR: i64 = 8;

    /// The integer `n`.
    pub fn int(n: i64) -> Word {
        Word {
            tag: Word::INT,
            bits: n,
        }
    }

    /// A port's state.
    pub fn state() -> Word {
        Word {
            tag: Word::STATE,
            bits: 0,
        }
    }

    /// The error word.
    pub fn err() -> Word {
        Word {
            tag: Word::ERR,
            bits: 0,
        }
    }

    /// The word of a scalar value, when `v` is one.
    pub fn scalar(v: &Value) -> Option<Word> {
        Some(match v {
            Value::Int(n) => Word::int(*n),
            Value::Float(x) => Word {
                tag: Word::FLOAT,
                bits: x.get().to_bits() as i64,
            },
            Value::Bool(b) => Word {
                tag: Word::BOOL,
                bits: i64::from(*b),
            },
            _ => return None,
        })
    }

    /// The word of entry `i` of the table.
    fn val(i: usize) -> Word {
        Word {
            tag: Word::VAL,
            bits: i as i64,
        }
    }

    /// The word of cell `index` in generation `generation`.
    fn cell(index: usize, generation: u32) -> Word {
        Word {
            tag: Word::CELL,
            bits: index as i64 | i64::from(generation) << INDEX_BITS,
        }
    }

    /// The index of the cell of cell word `self`.
    fn index(self) -> usize {
        (self.bits & INDEX_MASK) as usize
    }

    /// The generation of the cell of cell word `self`.
    fn generation(self) -> u32 {
        (self.bits as u64 >> INDEX_BITS) as u32
    }
}

/// The bits of a cell word's payload that hold the cell's index; the rest hold its generation.
/// 2^40 cells would take 64 TiB for the cells alone, so no heap reaches it.
pub const INDEX_BITS: u32 = 40;

/// The index bits of a cell word's payload.
const INDEX_MASK: i64 = (1 << INDEX_BITS) - 1;

/// The generations a cell goes through. A cell freed in its last generation is not taken
/// again, so the generation of a word from any earlier one never matches the cell's again.
const GENERATIONS: u32 = 1 << (64 - INDEX_BITS);

/// What a cell holds.
// Complexity tradeoff: the naive form holds a kernel value in place and each sequence of words
// in a `Vec`, which makes `Obj` 56 bytes, the size of a kernel value, and each sequence 24
// bytes. Here the kernel value is boxed and each sequence is a boxed slice of exactly its
// length or a pair in place (`Parts`), so `Obj` is 48 bytes and the cell 80, 96 with feature
// `counts` (R16). Tradeoffs: a big integer, a rational, a keypath or a family takes one
// allocation of its own; on a list of pairs each holding a big integer, making a level costs
// 709 instructions against 772 before, since the pair beside it no longer allocates. Nothing
// is refused. Tests `l01_36_cranelift::deep_heap`.
#[derive(Clone, Debug)]
pub enum Obj {
    /// A string.
    Str(Text),
    /// A non-empty tuple.
    Tuple(Parts),
    /// An atom with a non-empty payload, its parts in the order of [`Atom::args`]; a bare
    /// atom and one with an empty payload, `#e()`, are entries of the table.
    Atom {
        /// The atom's name.
        name: Arc<str>,
        /// The field names of a struct payload, sorted; empty for a tuple payload.
        fields: Fields,
        /// The payload.
        args: Box<[Word]>,
    },
    /// A big integer, a rational, a keypath or a family, as the kernel holds it.
    Data(Box<Value>),
    /// A closure: the index of its lambda in the program's table, and its captures.
    Clo {
        /// The lambda.
        lambda: usize,
        /// The captures, in the lambda node's input order.
        caps: Box<[Word]>,
    },
}

impl Obj {
    /// The type of what the cell holds, as a survivor report names it.
    #[cfg(feature = "counts")]
    fn kind(&self) -> &'static str {
        match self {
            Obj::Str(_) => "String",
            Obj::Tuple(_) => "tuple",
            Obj::Atom { .. } => "atom",
            Obj::Data(v) => match **v {
                Value::Int(_) | Value::Big(_) => "int",
                Value::Rat(_) => "rat",
                Value::Path(_) => "keypath",
                Value::Family(_) => "family",
                _ => "kernel value",
            },
            Obj::Clo { .. } => "closure",
        }
    }

    fn parts(&self) -> &[Word] {
        match self {
            Obj::Tuple(xs) => xs,
            Obj::Atom { args, .. } => args,
            Obj::Clo { caps, .. } => caps,
            Obj::Str(_) | Obj::Data(_) => &[],
        }
    }
}

/// The parts of a tuple: a pair in place, any other number in a block of their own.
// Complexity tradeoff: the naive form keeps every tuple's parts in a `Vec` of their own: 24
// bytes in the cell, and a block of 32 bytes for a pair, one allocation per tuple (R16). Here
// a pair is held in the cell, in the 40 bytes of `Parts`, so making a pair allocates nothing
// beyond its cell; any other tuple is a boxed slice of exactly its length, with no growth
// slack. Tradeoffs: reading a part first tests which variant holds the parts, a two-way
// branch (matching a list of pairs: 381.6 instructions a level against 380.9 with a `Vec`,
// R16); a single part is boxed, since a third variant in place made each read a three-way
// branch, 389.6. Nothing is refused. Tests
// `l01_36_cranelift::deep_heap::a_level_of_a_list_of_pairs_is_one_small_cell`.
#[derive(Clone, Debug)]
pub enum Parts {
    /// Two parts.
    Two([Word; 2]),
    /// One part, or three or more.
    Many(Box<[Word]>),
}

impl Deref for Parts {
    type Target = [Word];

    fn deref(&self) -> &[Word] {
        match self {
            Parts::Two(ws) => ws,
            Parts::Many(ws) => ws,
        }
    }
}

impl From<&[Word]> for Parts {
    fn from(ws: &[Word]) -> Parts {
        match *ws {
            [a, b] => Parts::Two([a, b]),
            _ => Parts::Many(ws.into()),
        }
    }
}

impl From<Vec<Word>> for Parts {
    fn from(ws: Vec<Word>) -> Parts {
        match *ws {
            [a, b] => Parts::Two([a, b]),
            _ => Parts::Many(ws.into_boxed_slice()),
        }
    }
}

/// A heap cell: its count, its generation and whether it was ever shared in this generation,
/// its contents until it is freed, and the kernel sequence of a tuple's parts or an atom's
/// payload once made. A cell's contents do not change while it is live, and its parts live at
/// least as long, so the sequence holds until the cell is freed (COMPLEXITY.md R1). A string
/// keeps nothing: its kernel value is its `Text`, which the cell holds already.
// Complexity tradeoff: the naive slow path copies each input into a kernel value and back at
// every kernel call, O(size) per call, so a value of n words handed to the kernel n times
// costs O(n²) (R1: 47.8 times the instructions for 8 times the size). Here each tuple or atom
// cell keeps the kernel sequence made from it, set when a kernel result becomes cells or on
// the first read, cleared when the cell is freed, so a value is read once however often it is
// handed over, and a cell met on several paths (R6) is read once; the atom's name and field
// names come from the cell. Tradeoffs: 24 bytes in every cell (R16), and the memory of one
// kernel sequence per such cell while it lives, shared with the value's parts; correct only
// because a live cell's contents never change (the one write is the reuse of a freed slot,
// which clears the sequence). A map from cell index to sequence beside the cells costs 55 to
// 75 bytes per filled entry and a hash lookup at each read and each free; runs fill 37 to 84
// percent of tuple and atom cells (R16), so the map saves at most 4 bytes a cell at the
// lowest fill and costs up to 39 more at the highest. Nothing is refused. Tests
// `l01_36_cranelift::kernel_inputs`.
#[derive(Debug)]
struct Cell {
    count: u32,
    /// The generation, below [`GENERATIONS`], and [`SHARED`] when the count has exceeded 1 in
    /// this generation: one word for both, since a generation needs 24 bits.
    stamp: u32,
    obj: Option<Obj>,
    items: Option<Items>,
    /// The node that allocated it, none outside every node (feature `counts`).
    #[cfg(feature = "counts")]
    site: Option<usize>,
}

/// The bit of [`Cell::stamp`] that says the cell was shared in this generation.
const SHARED: u32 = 1 << 31;

const _: () = assert!(
    GENERATIONS <= SHARED,
    "a generation never reaches the shared bit"
);

impl Cell {
    /// The cell's generation.
    fn generation(&self) -> u32 {
        self.stamp & !SHARED
    }

    /// The kernel value the cell keeps: a tuple or an atom whose sequence it has made.
    fn kept(&self) -> Option<Value> {
        let items = self.items.as_ref()?;
        Some(match self.obj.as_ref()? {
            Obj::Atom { name, fields, .. } => Value::Atom(Atom {
                name: name.clone(),
                fields: fields.clone(),
                payload: Some(items.clone()),
            }),
            _ => Value::Tuple(items.clone()),
        })
    }
}

/// The sequence of a tuple or of an atom's payload.
fn items_of(v: &Value) -> Option<&Items> {
    match v {
        Value::Tuple(xs) => Some(xs),
        Value::Atom(a) => a.payload.as_ref(),
        _ => None,
    }
}

/// The bytes of one heap cell in the heap's table, its contents' own blocks not included: what a
/// boxed value costs beside its [`Word`] (the layout record, `zed/compiler/MLIR.md`). The build
/// with feature `counts` adds the allocating node.
pub const CELL_BYTES: usize = mem::size_of::<Cell>();

/// An entry of the table: an uncounted value, and where the entries of its parts start once a
/// match has read them.
// Complexity tradeoff: the naive table pushes every part a match reads, a deep clone of the
// constant at each match, O(size) memory per match and O(matches · size) in all (R3: 991
// entries after 10 matches at depth 100). Here an entry's parts are entered once, together,
// the first time a match reads them (`parts`), and later matches read them in place, so the
// table grows with the distinct constants and parts a run reads, not with its matches.
// Tradeoff: an entry is never freed (a VAL word has no count, R6), so the table keeps every
// part read until the run ends. Nothing is refused. Tests `l01_36_cranelift::reuse` and
// `l01_36_cranelift::scaling::matching_one_constant_many_times_scales`.
#[derive(Debug)]
struct Entry {
    value: Value,
    parts: Option<usize>,
}

/// The counts of one run, the same measures as the counting machine of step L1.34 keeps.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct Stats {
    /// Count increments.
    pub increments: u64,
    /// Count decrements.
    pub decrements: u64,
    /// Cells allocated.
    pub allocations: u64,
    /// Cells freed.
    pub frees: u64,
    /// The most cells live at once.
    pub peak: u64,
    /// The cells whose count ever exceeded 1.
    pub shared: u64,
    /// The words [`Heap::value`] read to make kernel values: one for a word whose value it had
    /// already made.
    pub converted: u64,
}

/// Live cells of one type allocated by one node, as [`Heap::survivors`] lists them (feature
/// `counts`).
#[cfg(feature = "counts")]
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Survivor {
    /// The type of what the cells hold.
    pub kind: &'static str,
    /// The node that allocated them, none outside every node.
    pub node: Option<usize>,
    /// How many there are.
    pub cells: u64,
}

/// A cell freed, as [`Heap::released`] lists them in the order they were freed (feature
/// `counts`).
#[cfg(feature = "counts")]
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Released {
    /// The type of what the cell held.
    pub kind: &'static str,
    /// The string it held, for a string.
    pub text: Option<Text>,
}

/// Where the parts of a tuple or an atom being matched are read: a live cell, or the entries
/// of the parts of entry `entry` of the table, from `start`.
#[derive(Clone, Copy)]
enum Holder {
    Cell(usize),
    Table { entry: usize, start: usize },
}

/// A tuple or an atom a structural pattern reads: its atom's name and field names, none for a
/// tuple; its number of parts; and where they are.
struct Shape<'h> {
    atom: Option<(&'h str, &'h [Arc<str>])>,
    /// Whether an atom has no payload, as `#e` has none and `#e()` has an empty one.
    bare: bool,
    len: usize,
    holder: Holder,
}

/// A tuple or an atom [`Heap::fresh`] has entered: its payload's atom, its parts still to make,
/// and where the words of those made start. Values nest as deep as a program builds them, so
/// the values in progress are on a stack.
struct Making<'v> {
    /// The value, which the cell keeps as its kernel value.
    value: &'v Value,
    /// The atom; none for a tuple.
    atom: Option<&'v Atom>,
    /// The shared sequence it holds, whose cell later meetings take; none when held once.
    shared: Option<SharedParts<'v>>,
    rest: slice::Iter<'v, Value>,
    /// Where its words start in the buffer of words made.
    start: usize,
}

/// A cell [`Heap::value`] has entered: its word, and the values of its parts read so far, which
/// also says which part is next.
struct Reading {
    w: Word,
    parts: Vec<Value>,
}

/// The sub-patterns of a pattern [`Heap::matches`] has entered.
enum Subs<'p> {
    /// Positional: pattern `i` reads part `i`.
    Items(&'p [Pattern]),
    /// Named: each pattern reads the part of its field among the atom's field names.
    Fields(&'p [(Arc<str>, Pattern)]),
}

/// A tuple or atom pattern [`Heap::matches`] has entered, with where the parts of the word it
/// reads are.
struct Matching<'p> {
    subs: Subs<'p>,
    holder: Holder,
    /// The next sub-pattern.
    next: usize,
}

/// What reading one word against one pattern, without its sub-patterns, gives.
enum Shallow<'p> {
    /// It does not match.
    No,
    /// It matches, with nothing below.
    Yes,
    /// It matches so far; the sub-patterns decide.
    Below(Matching<'p>),
}

/// What cell `w` of `cells` holds; `None` for a word that is not a cell.
fn obj_in(cells: &[Cell], w: Word) -> Result<Option<&Obj>, String> {
    if w.tag != Word::CELL {
        return Ok(None);
    }
    let c = &cells[w.index()];
    match &c.obj {
        Some(o) if c.generation() == w.generation() => Ok(Some(o)),
        _ => Err(freed(Freed::Used, w.index())),
    }
}

/// The heap of one run.
#[derive(Debug, Default)]
pub struct Heap {
    cells: Vec<Cell>,
    /// The freed cells that can be taken again, the next on top.
    free: Vec<usize>,
    vals: Vec<Entry>,
    /// The entry of the empty tuple and of each bare atom.
    bare: BTreeMap<Value, usize>,
    /// The counts so far.
    pub stats: Stats,
    live: u64,
    /// The stack of words [`Heap::dec`] still has to drop, empty between calls.
    todo: Vec<Word>,
    /// The node whose allocations are being made, none outside every node (feature `counts`).
    #[cfg(feature = "counts")]
    site: Option<usize>,
    /// The cells freed, in order, once [`Heap::record_releases`] has asked for them (feature
    /// `counts`); none otherwise, so a run that does not ask keeps nothing per free.
    #[cfg(feature = "counts")]
    released: Option<Vec<Released>>,
}

impl Heap {
    /// An empty heap.
    pub fn new() -> Heap {
        Heap::default()
    }

    /// The cells live now.
    pub fn live(&self) -> u64 {
        self.live
    }

    /// The cells the heap holds, live or free: what its memory for cells grows with.
    pub fn cell_slots(&self) -> usize {
        self.cells.len()
    }

    /// The entries of the table of uncounted values.
    pub fn table_len(&self) -> usize {
        self.vals.len()
    }

    /// Records that the allocations from now on are made by `node`, none outside every node.
    /// Empty unless feature `counts` is on.
    #[inline]
    pub fn allocating(&mut self, node: Option<usize>) {
        #[cfg(feature = "counts")]
        {
            self.site = node;
        }
        #[cfg(not(feature = "counts"))]
        let _ = node;
    }

    /// The cells live now, grouped by their type and the node that allocated them, in that
    /// order (feature `counts`).
    #[cfg(feature = "counts")]
    pub fn survivors(&self) -> Vec<Survivor> {
        let mut groups: BTreeMap<(&'static str, Option<usize>), u64> = BTreeMap::new();
        for c in &self.cells {
            if let Some(o) = &c.obj {
                *groups.entry((o.kind(), c.site)).or_default() += 1;
            }
        }
        groups
            .into_iter()
            .map(|((kind, node), cells)| Survivor { kind, node, cells })
            .collect()
    }

    /// Records each cell freed from now on, in order, for [`Heap::released`] (feature
    /// `counts`). O(1) per free.
    #[cfg(feature = "counts")]
    pub fn record_releases(&mut self) {
        self.released.get_or_insert_with(Vec::new);
    }

    /// The cells freed since [`Heap::record_releases`], in the order they were freed, taken
    /// out of the record (feature `counts`).
    #[cfg(feature = "counts")]
    pub fn released(&mut self) -> Vec<Released> {
        self.released.as_mut().map(mem::take).unwrap_or_default()
    }

    /// The word of `v`, uncounted: a scalar, or an entry of the table. The empty tuple, a bare
    /// atom and an atom with an empty payload made again are the entry they had.
    pub fn uncounted(&mut self, v: Value) -> Word {
        if let Some(w) = Word::scalar(&v) {
            return w;
        }
        let bare = match &v {
            Value::Tuple(xs) => xs.is_empty(),
            Value::Atom(a) => a.args().is_empty(),
            _ => false,
        };
        if bare {
            if let Some(&i) = self.bare.get(&v) {
                return Word::val(i);
            }
            self.bare.insert(v.clone(), self.vals.len());
        }
        self.vals.push(Entry {
            value: v,
            parts: None,
        });
        Word::val(self.vals.len() - 1)
    }

    /// The uncounted value of word `w`, tagged [`Word::VAL`].
    pub fn value_ref(&self, w: Word) -> &Value {
        &self.vals[w.bits as usize].value
    }

    /// The word of entry `i` of the table: the scalar it holds, or the entry.
    fn table_word(&self, i: usize) -> Word {
        Word::scalar(&self.vals[i].value).unwrap_or(Word::val(i))
    }

    /// Where the entries of the parts of entry `i` start, entered together the first time.
    fn table_parts(&mut self, i: usize) -> usize {
        if let Some(start) = self.vals[i].parts {
            return start;
        }
        // The table shares the parts with the entry, a count each.
        let items = match &self.vals[i].value {
            Value::Tuple(xs) => xs.clone(),
            Value::Atom(a) => a.args().clone(),
            _ => Items::default(),
        };
        let start = self.vals.len();
        self.vals.extend(items.iter().map(|x| Entry {
            value: x.clone(),
            parts: None,
        }));
        self.vals[i].parts = Some(start);
        start
    }

    /// A new cell holding `obj`, with count 1: a freed cell when there is one.
    pub fn alloc(&mut self, obj: Obj) -> Word {
        self.stats.allocations += 1;
        self.live += 1;
        self.stats.peak = self.stats.peak.max(self.live);
        let i = match self.free.pop() {
            Some(i) => {
                let c = &mut self.cells[i];
                (c.count, c.obj) = (1, Some(obj));
                #[cfg(feature = "counts")]
                {
                    c.site = self.site;
                }
                i
            }
            None => {
                self.cells.push(Cell {
                    count: 1,
                    stamp: 0,
                    obj: Some(obj),
                    items: None,
                    #[cfg(feature = "counts")]
                    site: self.site,
                });
                self.cells.len() - 1
            }
        };
        Word::cell(i, self.cells[i].generation())
    }

    /// Frees cell `i`, whose count has reached 0: its contents, which it gives back, and its
    /// kernel value go, and its generation advances.
    fn free_cell(&mut self, i: usize) -> Obj {
        let c = &mut self.cells[i];
        let obj = c.obj.take().expect("a live cell holds its contents");
        c.items = None;
        // The next generation, not yet shared.
        c.stamp = c.generation() + 1;
        if c.stamp < GENERATIONS {
            self.free.push(i);
        }
        self.stats.frees += 1;
        self.live -= 1;
        #[cfg(feature = "counts")]
        if let Some(r) = &mut self.released {
            r.push(Released {
                kind: obj.kind(),
                text: match &obj {
                    Obj::Str(t) => Some(t.clone()),
                    _ => None,
                },
            });
        }
        obj
    }

    /// A fresh word for `v`, owned: its cells allocated as the counting machine allocates a
    /// value the kernel returns. A tuple or an atom whose sequence `v` holds in several places is
    /// one cell, counted once per holder, so a value whose levels each hold the one below twice
    /// costs a cell per level, not one per path (COMPLEXITY.md R9); every other part is its
    /// own. Each cell keeps its part of `v` as its kernel value, so handing it to the kernel
    /// again reads nothing.
    // Complexity tradeoff: the naive form gives each occurrence of a part its own cell, so a
    // value whose d levels each hold the one below twice costs 2^d cells and time (R9: 4 times
    // per 2 levels). Here the cell of each shared sequence is kept in `made`, keyed by the
    // sequence's identity (`Value::shared_parts`), and a second holder takes an increment:
    // O(distinct sequences + holders). Tradeoffs: one map entry per shared sequence for the
    // call; equal sequences built apart get cells of their own, since only identity is
    // compared, as the counting machine does. Nothing is refused. Tests
    // `l01_36_cranelift::shared_values`.
    pub fn fresh(&mut self, v: &Value) -> Result<Word, String> {
        let mut stack: Vec<Making<'_>> = Vec::new();
        // The words made of the values on the stack, each value's from its `start`: one buffer,
        // so a level allocates nothing for its words but its cell's own block, if any.
        let mut words: Vec<Word> = Vec::new();
        // The cell of each shared sequence made so far, by the sequence's identity.
        let mut made: HashMap<SharedParts<'_>, Word> = HashMap::new();
        let mut next = v;
        loop {
            let (atom, items): (_, &[Value]) = match next {
                Value::Tuple(xs) => (None, xs),
                Value::Atom(a) => (Some(a), a.args()),
                _ => (None, &[]),
            };
            let shared = next.shared_parts();
            let mut rest = items.iter();
            let mut w = match shared.and_then(|k| made.get(&k)) {
                Some(&w) => {
                    self.inc(w)?;
                    w
                }
                None => {
                    if let Some(first) = rest.next() {
                        stack.push(Making {
                            value: next,
                            atom,
                            shared,
                            rest,
                            start: words.len(),
                        });
                        next = first;
                        continue;
                    }
                    self.fresh_leaf(next)
                }
            };
            // Each finished value is a part of the one below it on the stack.
            loop {
                let Some(top) = stack.last_mut() else {
                    return Ok(w);
                };
                words.push(w);
                if let Some(x) = top.rest.next() {
                    next = x;
                    break;
                }
                let m = stack.pop().expect("the stack has a top");
                let parts = &words[m.start..];
                let obj = match m.atom {
                    None => Obj::Tuple(parts.into()),
                    Some(a) => Obj::Atom {
                        name: a.name.clone(),
                        fields: a.fields.clone(),
                        args: parts.into(),
                    },
                };
                words.truncate(m.start);
                w = self.alloc(obj);
                self.cells[w.index()].items = items_of(m.value).cloned();
                if let Some(k) = m.shared {
                    made.insert(k, w);
                }
            }
        }
    }

    /// The fresh word of `v`, which has no parts of its own.
    fn fresh_leaf(&mut self, v: &Value) -> Word {
        if let Some(w) = Word::scalar(v) {
            return w;
        }
        match v {
            Value::Tuple(_) | Value::Atom(_) => self.uncounted(v.clone()),
            Value::Str(s) => self.alloc(Obj::Str(s.clone())),
            _ => self.alloc(Obj::Data(Box::new(v.clone()))),
        }
    }

    /// What live cell `w` holds; `None` for a word that is not a cell.
    pub fn obj(&self, w: Word) -> Result<Option<&Obj>, String> {
        obj_in(&self.cells, w)
    }

    /// Whether `w` is a function: a closure, a primitive or a lookup port.
    pub fn is_function(&self, w: Word) -> Result<bool, String> {
        Ok(match w.tag {
            Word::PRIM | Word::SOURCE => true,
            Word::CELL => matches!(self.obj(w)?, Some(Obj::Clo { .. })),
            _ => false,
        })
    }

    /// The kernel value of data word `w`; a string is shared, not written out. Each tuple or atom
    /// cell keeps the sequence made from it until it is freed, so a cell met again, on another
    /// path or in a later call, is read once: the value shares its parts as the cells do, and a
    /// value handed to the kernel many times costs its size once (COMPLEXITY.md R1).
    pub fn value(&mut self, w: Word) -> Result<Value, String> {
        let mut stack = Vec::new();
        let mut made = self.read(w, &mut stack)?;
        loop {
            let Some(top) = stack.last_mut() else {
                return Ok(made.expect("an empty stack follows a finished value"));
            };
            top.parts.extend(made.take());
            let parts = self.obj(top.w)?.map_or(&[][..], Obj::parts);
            match parts.get(top.parts.len()) {
                Some(&part) => made = self.read(part, &mut stack)?,
                None => {
                    let r = stack.pop().expect("the stack has a top");
                    let items = Items::from(r.parts);
                    let v = match self.obj(r.w)? {
                        Some(Obj::Atom { name, fields, .. }) => Value::Atom(Atom {
                            name: name.clone(),
                            fields: fields.clone(),
                            payload: Some(items.clone()),
                        }),
                        _ => Value::Tuple(items.clone()),
                    };
                    self.cells[r.w.index()].items = Some(items);
                    made = Some(v);
                }
            }
        }
    }

    /// The value of `w` when it has no parts to read or its cell keeps its value; otherwise
    /// enters it on `stack`.
    fn read(&mut self, w: Word, stack: &mut Vec<Reading>) -> Result<Option<Value>, String> {
        self.stats.converted += 1;
        Ok(Some(match w.tag {
            Word::INT => Value::Int(w.bits),
            Word::FLOAT => Value::float(f64::from_bits(w.bits as u64)),
            Word::BOOL => Value::Bool(w.bits != 0),
            Word::VAL => self.vals[w.bits as usize].value.clone(),
            Word::CELL => match obj_in(&self.cells, w)? {
                _ if let Some(v) = self.cells[w.index()].kept() => v,
                Some(Obj::Str(r)) => Value::Str(r.clone()),
                Some(o @ (Obj::Tuple(_) | Obj::Atom { .. })) => {
                    stack.push(Reading {
                        w,
                        parts: Vec::with_capacity(o.parts().len()),
                    });
                    return Ok(None);
                }
                Some(Obj::Data(v)) => (**v).clone(),
                Some(Obj::Clo { .. }) => return Err(closure_as_data()),
                None => unreachable!("obj_in checks the cell is live"),
            },
            t => return Err(not_data(t)),
        }))
    }

    /// Adds a reference to `w`, when it is a cell: an error for a cell already freed, and for
    /// one whose count is at the most it can hold. The error is returned here, so it does not
    /// wait for a later write that may never come.
    pub fn inc(&mut self, w: Word) -> Result<(), String> {
        if w.tag != Word::CELL {
            return Ok(());
        }
        let c = &mut self.cells[w.index()];
        if c.count == 0 || c.generation() != w.generation() {
            return Err(freed(Freed::Shared, w.index()));
        }
        c.count = c
            .count
            .checked_add(1)
            .ok_or_else(|| full_count(w.index()))?;
        self.stats.increments += 1;
        if c.count == 2 && c.stamp & SHARED == 0 {
            c.stamp |= SHARED;
            self.stats.shared += 1;
        }
        Ok(())
    }

    /// Drops a reference to `w`, when it is a cell, freeing it and dropping its parts at 0.
    /// Work beyond the one count write happens only when a cell with parts is freed, and that
    /// work is paid for by the cell's allocation.
    pub fn dec(&mut self, w: Word) -> Result<(), String> {
        let Some(obj) = self.drop_ref(w)? else {
            return Ok(());
        };
        if obj.parts().is_empty() {
            return Ok(());
        }
        // The stack keeps its capacity across calls. An error ends the run, so that path
        // leaves `self.todo` empty and gives up only the capacity.
        let mut todo = mem::take(&mut self.todo);
        // In reverse, so the parts are dropped first to last.
        todo.extend(obj.parts().iter().rev().copied());
        while let Some(w) = todo.pop() {
            if let Some(obj) = self.drop_ref(w)? {
                todo.extend(obj.parts().iter().rev().copied());
            }
        }
        self.todo = todo;
        Ok(())
    }

    /// Writes one decrement of `w`, when it is a cell; gives back the contents of a cell that
    /// reached 0.
    fn drop_ref(&mut self, w: Word) -> Result<Option<Obj>, String> {
        if w.tag != Word::CELL {
            return Ok(None);
        }
        self.stats.decrements += 1;
        let c = &mut self.cells[w.index()];
        if c.count == 0 || c.generation() != w.generation() {
            return Err(freed(Freed::Dropped, w.index()));
        }
        c.count -= 1;
        if c.count > 0 {
            return Ok(None);
        }
        Ok(Some(self.free_cell(w.index())))
    }

    /// The fused release of step L1.34 of scrutinee `w`, keeping the parts at the nodes `kept`
    /// of `paths`: a cell with count 1 is freed without a count write, the kept parts'
    /// references moving out of it and the others dropped; a shared cell gives each kept part a
    /// reference and loses one. O(cells freed + nodes of `paths`): each node on the way to a
    /// kept part is read once, where a list of paths read each path from the top, O(d²) for a
    /// binder at each of `d` levels (HEAP-binder-paths).
    pub fn release(&mut self, w: Word, paths: &Paths, kept: &[usize]) -> Result<(), String> {
        let tree = Kept::new(paths, kept);
        let mut todo = Vec::new();
        self.release_one(w, &tree, &[Paths::ROOT], &mut todo)?;
        // An empty list of nodes on the stack is a part nothing keeps.
        while let Some((part, sub)) = todo.pop() {
            if sub.is_empty() {
                self.dec(part)?;
            } else {
                self.release_one(part, &tree, &sub, &mut todo)?;
            }
        }
        Ok(())
    }

    /// One cell of a fused release, at the nodes `at` of `tree`: the parts of a cell it frees
    /// go on `todo`, the first on top, each with its nodes on the way to a kept part.
    fn release_one(
        &mut self,
        w: Word,
        tree: &Kept<'_>,
        at: &[usize],
        todo: &mut Vec<(Word, Vec<usize>)>,
    ) -> Result<(), String> {
        if w.tag != Word::CELL || at.iter().any(|&x| tree.kept(x)) {
            return Ok(());
        }
        self.obj(w)?;
        let c = &mut self.cells[w.index()];
        if c.count == 1 {
            c.count = 0;
            let obj = self.free_cell(w.index());
            let parts = obj.parts();
            // Each child goes to the part it reads, in one step.
            let mut sub = vec![Vec::new(); parts.len()];
            for kid in at.iter().flat_map(|&x| tree.kids(x)) {
                let i = tree.part(kid);
                let Some(s) = sub.get_mut(i) else {
                    return Err(crate::bug::bug(
                        "released a value and kept a part of it that the value does not have",
                        &format!(
                            "a kept path reads part {i} of a cell of {} parts",
                            parts.len()
                        ),
                    ));
                };
                s.push(kid);
            }
            todo.extend(parts.iter().copied().zip(sub).rev());
        } else {
            for &x in at {
                self.inc_kept(w, tree, x)?;
            }
            self.dec(w)?;
        }
        Ok(())
    }

    /// Gives each kept part below node `x` of `tree`, which is at word `w`, a reference, in
    /// preorder. A constant on the way stops the walk below it: every part of a constant is a
    /// constant, which [`Heap::inc`] does not count. Paths nest as deep as patterns, so the
    /// parts in progress are on a stack.
    fn inc_kept(&mut self, w: Word, tree: &Kept<'_>, x: usize) -> Result<(), String> {
        let mut todo: Vec<(Word, usize)> = Vec::new();
        let push = |todo: &mut Vec<(Word, usize)>, w: Word, x: usize| {
            let start = todo.len();
            todo.extend(tree.kids(x).map(|k| (w, k)));
            todo[start..].reverse();
        };
        push(&mut todo, w, x);
        while let Some((holder, k)) = todo.pop() {
            if holder.tag == Word::VAL {
                continue;
            }
            let part = match self.obj(holder)? {
                Some(o) => o.parts()[tree.part(k)],
                None => {
                    return Err(crate::bug::bug(
                        "kept a part of a value that has no parts",
                        &format!("a word tagged {} has no parts", holder.tag),
                    ));
                }
            };
            if tree.kept(k) {
                self.inc(part)?;
            } else {
                push(&mut todo, part, k);
            }
        }
        Ok(())
    }

    /// Part `i` of closure `w`, borrowed: a capture.
    pub fn capture(&self, w: Word, i: usize) -> Result<Word, String> {
        match self.obj(w)? {
            Some(Obj::Clo { caps, .. }) => Ok(caps[i]),
            _ => Err(crate::bug::bug(
                "called something that is not a function",
                &format!("a word tagged {} is not a closure", w.tag),
            )),
        }
    }

    /// The tuple or atom data word `w` is, for a structural pattern; `None` for any other word.
    /// The parts of an entry of the table are entered the first time.
    fn shape(&mut self, w: Word) -> Result<Option<Shape<'_>>, String> {
        let (atom, bare, len, holder) = match w.tag {
            Word::CELL => {
                let holder = Holder::Cell(w.index());
                match obj_in(&self.cells, w)? {
                    Some(Obj::Tuple(xs)) => (None, false, xs.len(), holder),
                    Some(Obj::Atom { name, fields, args }) => {
                        (Some((&**name, &**fields)), false, args.len(), holder)
                    }
                    _ => return Ok(None),
                }
            }
            Word::VAL => {
                let entry = w.bits as usize;
                if !matches!(self.vals[entry].value, Value::Tuple(_) | Value::Atom(_)) {
                    return Ok(None);
                }
                let start = self.table_parts(entry);
                let holder = Holder::Table { entry, start };
                match &self.vals[entry].value {
                    Value::Tuple(xs) => (None, false, xs.len(), holder),
                    Value::Atom(a) => {
                        let atom = Some((&*a.name, &*a.fields));
                        (atom, a.is_bare(), a.args().len(), holder)
                    }
                    _ => unreachable!("checked a tuple or an atom"),
                }
            }
            _ => return Ok(None),
        };
        Ok(Some(Shape {
            atom,
            bare,
            len,
            holder,
        }))
    }

    /// Part `i` of the tuple or atom in `h`.
    fn part(&self, h: Holder, i: usize) -> Word {
        match h {
            Holder::Cell(c) => {
                let o = self.cells[c].obj.as_ref();
                o.expect("a cell being matched is live").parts()[i]
            }
            Holder::Table { start, .. } => self.table_word(start + i),
        }
    }

    /// The field names of the atom in `h`, sorted; empty for a tuple payload.
    fn field_names(&self, h: Holder) -> &[Arc<str>] {
        match h {
            Holder::Cell(c) => match &self.cells[c].obj {
                Some(Obj::Atom { fields, .. }) => fields,
                _ => &[],
            },
            Holder::Table { entry, .. } => match &self.vals[entry].value {
                Value::Atom(a) => &a.fields,
                _ => &[],
            },
        }
    }

    /// Whether data word `w` equals `l`, read part by part against it, so the first difference
    /// ends the reading: a word of another kind than `l` is told by its tag.
    fn equals(&mut self, w: Word, l: &Value) -> Result<bool, String> {
        let mut todo = Vec::new();
        let (mut w, mut l) = (w, l);
        loop {
            let same = match w.tag {
                Word::INT | Word::FLOAT | Word::BOOL => Word::scalar(l) == Some(w),
                Word::VAL => self.vals[w.bits as usize].value == *l,
                Word::CELL => match obj_in(&self.cells, w)? {
                    Some(Obj::Str(r)) => match l {
                        // A join is read block by block, to the first byte that differs.
                        Value::Str(s) if r.len() == s.len() => r == s,
                        _ => false,
                    },
                    Some(Obj::Data(v)) => **v == *l,
                    Some(Obj::Tuple(xs)) => match l {
                        Value::Tuple(ys) if ys.len() == xs.len() => {
                            todo.extend(xs.iter().copied().zip(ys.iter()));
                            true
                        }
                        _ => false,
                    },
                    Some(Obj::Atom { name, fields, args }) => match l {
                        Value::Atom(a)
                            if a.name == *name
                                && a.fields == *fields
                                && a.args().len() == args.len() =>
                        {
                            todo.extend(args.iter().copied().zip(a.args().iter()));
                            true
                        }
                        _ => false,
                    },
                    Some(Obj::Clo { .. }) => return Err(closure_as_data()),
                    None => unreachable!("obj_in checks the cell is live"),
                },
                t => return Err(not_data(t)),
            };
            if !same {
                return Ok(false);
            }
            match todo.pop() {
                Some(next) => (w, l) = next,
                None => return Ok(true),
            }
        }
    }

    /// Whether data word `w` is in `t`. A constant and a value the kernel holds are read in
    /// place. A string, tuple or atom in cells is decided by its kind alone when `t` holds
    /// every value of that kind or none, so its text and parts are not read; otherwise it is
    /// made a value, which `t` reads whole.
    // Complexity tradeoff: the naive test makes the whole value of the cell and asks `t`,
    // O(size of the value) per test (R13: 8.0 times for 8 times the size). Here `t` is first
    // met with the cell's kind, O(size of `t`), and when `t` holds all of the kind or none of it
    // the answer needs no read of the value. Tradeoff: a `t` that holds part of the kind pays
    // the meet and then the full read, as before. Nothing is refused. Tests
    // `l01_36_cranelift::kinds`.
    fn is_in(&mut self, w: Word, t: &Type) -> Result<bool, String> {
        if w.tag == Word::VAL {
            return Ok(t.contains(&self.vals[w.bits as usize].value));
        }
        let kind = match self.obj(w)? {
            Some(Obj::Data(v)) => return Ok(t.contains(v)),
            Some(Obj::Str(_)) => Type::string(),
            Some(Obj::Tuple(_)) => Type::universe(Universe::Tuple),
            Some(Obj::Atom { name, .. }) => Type::atom(name) | Type::atom_with(name, &Type::top()),
            Some(Obj::Clo { .. }) | None => return Ok(t.contains(&self.value(w)?)),
        };
        let held = t & &kind;
        if held == kind {
            return Ok(true);
        }
        if held == Type::empty() {
            return Ok(false);
        }
        Ok(t.contains(&self.value(w)?))
    }

    /// Whether `w` matches `p`, as the kernel matches a value: `out` gets each binder's word
    /// and its node in `paths`, in preorder, and `paths` a node for each part entered, those
    /// before a failure included. A function matches only `_`, a name, and `is T` for a type
    /// `T` of functions. Patterns nest as deep as the source writes them, so the patterns in
    /// progress are on a stack, each with its next part.
    pub fn matches(
        &mut self,
        p: &Pattern,
        w: Word,
        paths: &mut Paths,
        out: &mut Vec<(Word, usize)>,
    ) -> Result<bool, String> {
        // The node of the part being read.
        let mut at = Paths::ROOT;
        let mut stack: Vec<Matching<'_>> = Vec::new();
        let (mut p, mut w) = (p, w);
        loop {
            let mut ended = match self.match_shallow(p, w, at, out)? {
                Shallow::No => return Ok(false),
                Shallow::Yes => true,
                Shallow::Below(m) => {
                    stack.push(m);
                    false
                }
            };
            loop {
                if ended {
                    // A pattern that has ended and is not the whole leaves its part.
                    if stack.is_empty() {
                        return Ok(true);
                    }
                    at = paths.parent(at);
                }
                let m = stack.last_mut().expect("a pattern is in progress");
                let k = m.next;
                m.next += 1;
                let next = match m.subs {
                    Subs::Items(ps) => ps.get(k).map(|q| (k, q)),
                    Subs::Fields(fs) => match fs.get(k) {
                        Some((f, q)) => match self.field_names(m.holder).binary_search(f) {
                            Ok(i) => Some((i, q)),
                            // A named field the word does not have.
                            Err(_) => return Ok(false),
                        },
                        None => None,
                    },
                };
                match next {
                    Some((i, q)) => {
                        w = self.part(m.holder, i);
                        p = q;
                        at = paths.push(at, i);
                        break;
                    }
                    None => {
                        stack.pop();
                        ended = true;
                    }
                }
            }
        }
    }

    /// Reads `w` against `p`, leaving any sub-patterns to [`Heap::matches`]; a binder gets the
    /// node `at`.
    fn match_shallow<'p>(
        &mut self,
        p: &'p Pattern,
        w: Word,
        at: usize,
        out: &mut Vec<(Word, usize)>,
    ) -> Result<Shallow<'p>, String> {
        let yes = |m: bool| if m { Shallow::Yes } else { Shallow::No };
        if self.is_function(w)? {
            return Ok(match p {
                Pattern::Wild => Shallow::Yes,
                Pattern::Bind(_) => {
                    out.push((w, at));
                    Shallow::Yes
                }
                Pattern::Is(t) => yes(t.functions()),
                _ => Shallow::No,
            });
        }
        let below = |subs, holder| {
            Shallow::Below(Matching {
                subs,
                holder,
                next: 0,
            })
        };
        Ok(match p {
            Pattern::Wild => Shallow::Yes,
            Pattern::Bind(_) => {
                out.push((w, at));
                Shallow::Yes
            }
            Pattern::Lit(l) => yes(self.equals(w, l)?),
            Pattern::AnyAtom => yes(matches!(self.shape(w)?, Some(Shape { atom: Some(_), .. }))),
            Pattern::Is(t) => yes(self.is_in(w, t)?),
            Pattern::Atom(name, ps) => match self.shape(w)? {
                // `#e` matches the bare atom only: a pattern has no `#e()` (sec:grammar).
                Some(Shape {
                    atom: Some((n, fields)),
                    bare,
                    len,
                    holder,
                }) if n == &**name
                    && fields.is_empty()
                    && len == ps.len()
                    && bare == ps.is_empty() =>
                {
                    below(Subs::Items(ps), holder)
                }
                _ => Shallow::No,
            },
            Pattern::Fields(name, fs) => match self.shape(w)? {
                Some(Shape {
                    atom: Some((n, fields)),
                    holder,
                    ..
                }) if n == &**name && !fields.is_empty() => below(Subs::Fields(fs), holder),
                _ => Shallow::No,
            },
            Pattern::Tuple(ps) => match self.shape(w)? {
                Some(Shape {
                    atom: None,
                    len,
                    holder,
                    ..
                }) if len == ps.len() => below(Subs::Items(ps), holder),
                _ => Shallow::No,
            },
        })
    }
}

/// What the compiled code did with a cell after freeing it.
enum Freed {
    Used,
    Shared,
    Dropped,
}

/// The message for a cell reached after it was freed: a bug in zedc, since the program's own
/// code never holds a released value.
fn freed(how: Freed, i: usize) -> String {
    let (what, did) = match how {
        Freed::Used => (
            "read a value after it had released the value's memory",
            "read",
        ),
        Freed::Shared => (
            "kept one more reference to a value after it had released the value's memory",
            "given a new reference",
        ),
        Freed::Dropped => ("released a value's memory twice", "dropped"),
    };
    crate::bug::bug(
        what,
        &format!("the heap's cell {i} was {did} after it was freed"),
    )
}

/// The message for a function read where a data value was expected.
fn closure_as_data() -> String {
    crate::bug::bug(
        "treated a function as a data value such as a number, a string, a tuple or a family",
        "a closure cell was read as data",
    )
}

/// The message for a word that holds no value read as a data value.
fn not_data(tag: i64) -> String {
    crate::bug::bug(
        "treated something that is not a value as a data value",
        &format!("a word tagged {tag} was read as data"),
    )
}

/// The message for a value held in more places than a reference count can count: a limit of
/// the native runtime, not a bug and not a fault of the program.
fn full_count(i: usize) -> String {
    format!(
        "the program stopped: one of its values is held in {} places at once, the most the \
         native runtime of a built executable can count for one value (the heap's cell {i}). The \
         program is not wrong; the limit is the runtime's. Repairs: run the program with `zedc \
         run`, which counts without this limit, or make fewer copies of that value live at the \
         same time, for example by passing it once to a function that does the repeated work",
        u32::MAX
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The nodes of one path, and the node at its end.
    fn one_path(p: &[usize]) -> (Paths, usize) {
        let mut paths = Paths::default();
        let end = p.iter().fold(Paths::ROOT, |at, &i| paths.push(at, i));
        (paths, end)
    }

    #[test]
    fn a_pair_of_strings_is_three_cells_and_frees_whole() {
        let mut h = Heap::new();
        let v = Value::tuple(vec![Value::str("a"), Value::str("b")]);
        let w = h.fresh(&v).unwrap();
        assert_eq!((h.stats.allocations, h.live()), (3, 3));
        assert_eq!(h.value(w).unwrap(), v);
        h.dec(w).unwrap();
        assert_eq!((h.stats.frees, h.live()), (3, 0));
        assert!(h.value(w).is_err(), "a use after free is caught");
        assert!(h.dec(w).is_err(), "a second drop is caught");
    }

    #[test]
    fn a_drop_uses_the_stack_only_to_free_a_cell_with_parts() {
        let mut h = Heap::new();
        h.dec(Word::int(3)).unwrap();
        assert_eq!(
            h.stats.decrements, 0,
            "a word that is not a cell is no write"
        );
        // A shared string, then the last reference to it.
        let s = h.fresh(&Value::str("a")).unwrap();
        h.inc(s).unwrap();
        h.dec(s).unwrap();
        assert_eq!((h.stats.decrements, h.live()), (1, 1));
        h.dec(s).unwrap();
        assert_eq!((h.stats.decrements, h.live()), (2, 0));
        assert_eq!(h.todo.capacity(), 0, "no stack was needed");
        // A nest of tuples: the stack grows once and is kept for the next free.
        let v = Value::tuple(vec![Value::tuple(vec![Value::str("a")]), Value::str("b")]);
        let w = h.fresh(&v).unwrap();
        h.dec(w).unwrap();
        assert_eq!(h.live(), 0);
        let cap = h.todo.capacity();
        assert!(cap > 0 && h.todo.is_empty());
        let w = h.fresh(&v).unwrap();
        h.dec(w).unwrap();
        assert_eq!((h.live(), h.todo.capacity()), (0, cap));
    }

    #[test]
    fn a_drop_after_a_free_inside_a_nest_is_an_error_and_the_next_drop_starts_clean() {
        let mut h = Heap::new();
        let s = h.fresh(&Value::str("a")).unwrap();
        let w = h.alloc(Obj::Tuple(vec![s, s].into()));
        assert_eq!(h.dec(w).unwrap_err(), freed(Freed::Dropped, s.index()));
        assert!(h.todo.is_empty());
        let w = h.fresh(&Value::tuple(vec![Value::str("b")])).unwrap();
        h.dec(w).unwrap();
        assert_eq!(h.live(), 0);
    }

    #[test]
    fn fused_release_keeps_one_part_with_no_count_write() {
        let mut h = Heap::new();
        let w = h
            .fresh(&Value::tuple(vec![Value::str("a"), Value::str("b")]))
            .unwrap();
        let mut out = Vec::new();
        let p = Pattern::Tuple(vec![Pattern::Bind("x".into()), Pattern::Wild]);
        let mut paths = Paths::default();
        assert!(h.matches(&p, w, &mut paths, &mut out).unwrap());
        assert_eq!(paths.path(out[0].1), vec![0]);
        h.release(w, &paths, &[out[0].1]).unwrap();
        // The pair is freed without a write, `b` dropped once; `a` is kept, uncounted.
        assert_eq!(
            (h.stats.increments, h.stats.decrements, h.live()),
            (0, 1, 1)
        );
        assert_eq!(h.value(out[0].0).unwrap(), Value::str("a"));
    }

    #[test]
    fn a_shared_release_stops_at_a_constant_and_writes_no_count_for_it() {
        let mut h = Heap::new();
        let k = h.uncounted(Value::tuple(vec![Value::Int(1), Value::str("x")]));
        let t = h.alloc(Obj::Tuple(vec![k, Word::int(2)].into()));
        h.inc(t).unwrap();
        let (paths, end) = one_path(&[0, 1]);
        h.release(t, &paths, &[end]).unwrap();
        assert_eq!((h.stats.increments, h.stats.decrements), (1, 1));
        assert_eq!(h.live(), 1);
    }

    #[test]
    fn a_path_into_a_scalar_is_an_error() {
        let mut h = Heap::new();
        let t = h.alloc(Obj::Tuple(vec![Word::int(1)].into()));
        h.inc(t).unwrap();
        let (paths, end) = one_path(&[0, 0]);
        assert_eq!(
            h.release(t, &paths, &[end]).unwrap_err(),
            crate::bug::bug(
                "kept a part of a value that has no parts",
                "a word tagged 0 has no parts"
            )
        );
    }

    /// `#e()` is an entry of the table apart from `#e`, made again as the entry it had, like the
    /// bare atom; the pattern `#e` matches the bare atom only, `#e(_)` neither, and `==` and
    /// `is` tell the two apart. No cell is allocated for either.
    #[test]
    fn an_empty_payload_is_an_entry_apart_from_the_bare_atom() {
        let mut h = Heap::new();
        let (bare, empty) = (Value::atom("e"), Value::atom_with("e", vec![]));
        let b = h.fresh(&bare).unwrap();
        let e = h.fresh(&empty).unwrap();
        assert_ne!(b, e);
        assert_eq!(h.uncounted(empty.clone()), e);
        assert_eq!(h.uncounted(bare.clone()), b);
        assert_eq!(
            (h.value(b).unwrap(), h.value(e).unwrap()),
            (bare.clone(), empty.clone())
        );
        let mut matched = |p: &Pattern, w: Word| {
            h.matches(p, w, &mut Paths::default(), &mut Vec::new())
                .unwrap()
        };
        let p = Pattern::Atom("e".into(), vec![]);
        assert!(matched(&p, b) && !matched(&p, e));
        let q = Pattern::Atom("e".into(), vec![Pattern::Wild]);
        assert!(!matched(&q, b) && !matched(&q, e));
        let unit = Type::atom_with("e", &Type::tuple(vec![]));
        assert!(matched(&Pattern::Is(unit.clone()), e) && !matched(&Pattern::Is(unit), b));
        let just = Type::atom("e");
        assert!(matched(&Pattern::Is(just.clone()), b) && !matched(&Pattern::Is(just), e));
        assert!(!h.equals(e, &bare).unwrap() && h.equals(e, &empty).unwrap());
        assert_eq!(h.stats.allocations, 0);
    }

    #[test]
    fn constants_match_without_cells() {
        let mut h = Heap::new();
        let w = h.uncounted(Value::atom_with("some", vec![Value::Int(3)]));
        let mut out = Vec::new();
        let p = Pattern::Atom("some".into(), vec![Pattern::Bind("n".into())]);
        assert!(h.matches(&p, w, &mut Paths::default(), &mut out).unwrap());
        assert_eq!(out[0].0, Word::int(3));
        let q = Pattern::Atom("none".into(), vec![]);
        assert!(
            !h.matches(&q, w, &mut Paths::default(), &mut Vec::new())
                .unwrap()
        );
        assert_eq!(h.stats.allocations, 0);
    }

    #[test]
    fn a_count_at_its_most_is_an_error_at_the_inc_itself() {
        let mut h = Heap::new();
        let w = h.alloc(Obj::Str("a".into()));
        h.cells[0].count = u32::MAX;
        let full = full_count(0);
        assert!(full.contains("held in 4294967295 places at once") && full.contains("`zedc run`"));
        assert_eq!(h.inc(w).unwrap_err(), full);
        assert_eq!(h.cells[0].count, u32::MAX);
        // A drop after the fault is an ordinary drop: the fault was not kept for it.
        h.dec(w).unwrap();
        assert_eq!(h.cells[0].count, u32::MAX - 1);
    }

    #[test]
    fn a_cell_freed_in_its_last_generation_is_not_taken_again() {
        let mut h = Heap::new();
        let w = h.alloc(Obj::Str("a".into()));
        h.dec(w).unwrap();
        let w = h.alloc(Obj::Str("b".into()));
        assert_eq!((w.index(), w.generation()), (0, 1));
        h.cells[0].stamp = GENERATIONS - 1;
        let last = Word::cell(0, GENERATIONS - 1);
        h.dec(last).unwrap();
        let next = h.alloc(Obj::Str("c".into()));
        assert_eq!((next.index(), next.generation()), (1, 0));
        assert_eq!(h.dec(last).unwrap_err(), freed(Freed::Dropped, 0));
    }
}
