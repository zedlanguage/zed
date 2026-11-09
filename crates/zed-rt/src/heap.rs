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
#[derive(Clone, Debug)]
pub enum Obj {
    /// A string.
    Str(Text),
    /// A non-empty tuple.
    Tuple(Vec<Word>),
    /// An atom with a payload, its parts in the order of [`Atom::args`].
    Atom {
        /// The atom's name.
        name: Arc<str>,
        /// The field names of a struct payload, sorted; empty for a tuple payload.
        fields: Fields,
        /// The payload.
        args: Vec<Word>,
    },
    /// A big integer, a rational, a keypath or a family, as the kernel holds it.
    Data(Value),
    /// A closure: the index of its lambda in the program's table, and its captures.
    Clo {
        /// The lambda.
        lambda: usize,
        /// The captures, in the lambda node's input order.
        caps: Vec<Word>,
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
            Obj::Data(Value::Int(_) | Value::Big(_)) => "int",
            Obj::Data(Value::Rat(_)) => "rat",
            Obj::Data(Value::Path(_)) => "keypath",
            Obj::Data(Value::Family(_)) => "family",
            Obj::Data(_) => "kernel value",
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

    fn take_parts(self) -> Vec<Word> {
        match self {
            Obj::Tuple(xs) => xs,
            Obj::Atom { args, .. } => args,
            Obj::Clo { caps, .. } => caps,
            Obj::Str(_) | Obj::Data(_) => Vec::new(),
        }
    }
}

/// A heap cell: its count, its generation, its contents until it is freed, whether it was ever
/// shared in this generation, and the kernel value of a string, tuple or atom once made. A
/// cell's contents do not change while it is live, and its parts live at least as long, so the
/// value holds until the cell is freed (COMPLEXITY.md R1).
#[derive(Debug)]
struct Cell {
    count: u32,
    generation: u32,
    obj: Option<Obj>,
    shared: bool,
    value: Option<Value>,
    /// The node that allocated it, none outside every node (feature `counts`).
    #[cfg(feature = "counts")]
    site: Option<usize>,
}

/// The bytes of one heap cell in the heap's table, its contents' own blocks not included: what a
/// boxed value costs beside its [`Word`] (the layout record, `zed/compiler/MLIR.md`). The build
/// with feature `counts` adds the allocating node.
pub const CELL_BYTES: usize = mem::size_of::<Cell>();

/// An entry of the table: an uncounted value, and where the entries of its parts start once a
/// match has read them.
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
    len: usize,
    holder: Holder,
}

/// A tuple or an atom [`Heap::fresh`] has entered: its payload's atom, its parts still to make,
/// and the words of those made. Values nest as deep as a program builds them, so the values in
/// progress are on a stack.
struct Making<'v> {
    /// The value, which the cell keeps as its kernel value.
    value: &'v Value,
    /// The atom; none for a tuple.
    atom: Option<&'v Atom>,
    /// The shared sequence it holds, whose cell later meetings take; none when held once.
    shared: Option<SharedParts<'v>>,
    rest: slice::Iter<'v, Value>,
    parts: Vec<Word>,
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
        Some(o) if c.generation == w.generation() => Ok(Some(o)),
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

    /// The word of `v`, uncounted: a scalar, or an entry of the table. The empty tuple and a
    /// bare atom made again are the entry they had.
    pub fn uncounted(&mut self, v: Value) -> Word {
        if let Some(w) = Word::scalar(&v) {
            return w;
        }
        let bare = match &v {
            Value::Tuple(xs) => xs.is_empty(),
            Value::Atom(a) => a.args.is_empty(),
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
            Value::Atom(a) => a.args.clone(),
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
                (c.count, c.obj, c.shared) = (1, Some(obj), false);
                #[cfg(feature = "counts")]
                {
                    c.site = self.site;
                }
                i
            }
            None => {
                self.cells.push(Cell {
                    count: 1,
                    generation: 0,
                    obj: Some(obj),
                    shared: false,
                    value: None,
                    #[cfg(feature = "counts")]
                    site: self.site,
                });
                self.cells.len() - 1
            }
        };
        Word::cell(i, self.cells[i].generation)
    }

    /// Frees cell `i`, whose count has reached 0: its contents, which it gives back, and its
    /// kernel value go, and its generation advances.
    fn free_cell(&mut self, i: usize) -> Obj {
        let c = &mut self.cells[i];
        let obj = c.obj.take().expect("a live cell holds its contents");
        c.value = None;
        c.generation += 1;
        if c.generation < GENERATIONS {
            self.free.push(i);
        }
        self.stats.frees += 1;
        self.live -= 1;
        obj
    }

    /// A fresh word for `v`, owned: its cells allocated as the counting machine allocates a
    /// value the kernel returns. A tuple or an atom whose sequence `v` holds in several places is
    /// one cell, counted once per holder, so a value whose levels each hold the one below twice
    /// costs a cell per level, not one per path (COMPLEXITY.md R9); every other part is its
    /// own. Each cell keeps its part of `v` as its kernel value, so handing it to the kernel
    /// again reads nothing.
    pub fn fresh(&mut self, v: &Value) -> Result<Word, String> {
        let mut stack: Vec<Making<'_>> = Vec::new();
        // The cell of each shared sequence made so far, by the sequence's identity.
        let mut made: HashMap<SharedParts<'_>, Word> = HashMap::new();
        let mut next = v;
        loop {
            let (atom, items): (_, &[Value]) = match next {
                Value::Tuple(xs) => (None, xs),
                Value::Atom(a) => (Some(a), &a.args),
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
                            parts: Vec::with_capacity(items.len()),
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
                top.parts.push(w);
                if let Some(x) = top.rest.next() {
                    next = x;
                    break;
                }
                let m = stack.pop().expect("the stack has a top");
                w = self.alloc(match m.atom {
                    None => Obj::Tuple(m.parts),
                    Some(a) => Obj::Atom {
                        name: a.name.clone(),
                        fields: a.fields.clone(),
                        args: m.parts,
                    },
                });
                self.cells[w.index()].value = Some(m.value.clone());
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
            Value::Str(s) => {
                let w = self.alloc(Obj::Str(s.clone()));
                self.cells[w.index()].value = Some(v.clone());
                w
            }
            _ => self.alloc(Obj::Data(v.clone())),
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

    /// The kernel value of data word `w`; a string is shared, not written out. Each string,
    /// tuple or atom cell keeps the value made from it until it is freed, so a cell met again,
    /// on another path or in a later call, is read once: the value shares its parts as the cells
    /// do, and a value handed to the kernel many times costs its size once (COMPLEXITY.md R1).
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
                    let v = match self.obj(r.w)? {
                        Some(Obj::Atom { name, fields, .. }) => Value::Atom(Atom {
                            name: name.clone(),
                            fields: fields.clone(),
                            args: r.parts.into(),
                        }),
                        _ => Value::Tuple(r.parts.into()),
                    };
                    self.cells[r.w.index()].value = Some(v.clone());
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
                _ if let Some(v) = &self.cells[w.index()].value => v.clone(),
                Some(Obj::Str(r)) => Value::Str(r.clone()),
                Some(o @ (Obj::Tuple(_) | Obj::Atom { .. })) => {
                    stack.push(Reading {
                        w,
                        parts: Vec::with_capacity(o.parts().len()),
                    });
                    return Ok(None);
                }
                Some(Obj::Data(v)) => v.clone(),
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
        if c.count == 0 || c.generation != w.generation() {
            return Err(freed(Freed::Shared, w.index()));
        }
        c.count = c
            .count
            .checked_add(1)
            .ok_or_else(|| full_count(w.index()))?;
        self.stats.increments += 1;
        if c.count == 2 && !c.shared {
            c.shared = true;
            self.stats.shared += 1;
        }
        Ok(())
    }

    /// Drops a reference to `w`, when it is a cell, freeing it and dropping its parts at 0.
    /// Work beyond the one count write happens only when a cell with parts is freed, and that
    /// work is paid for by the parts' allocation.
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
        todo.extend(obj.take_parts().into_iter().rev());
        while let Some(w) = todo.pop() {
            if let Some(obj) = self.drop_ref(w)? {
                todo.extend(obj.take_parts().into_iter().rev());
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
        if c.count == 0 || c.generation != w.generation() {
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
            let parts = self.free_cell(w.index()).take_parts();
            // Each child goes to the part it reads, in one step.
            let mut sub = vec![Vec::new(); parts.len()];
            for kid in at.iter().flat_map(|&x| tree.kids(x)) {
                let i = tree.part(kid);
                let Some(s) = sub.get_mut(i) else {
                    return Err(crate::bug(
                        "released a value and kept a part of it that the value does not have",
                        &format!(
                            "a kept path reads part {i} of a cell of {} parts",
                            parts.len()
                        ),
                    ));
                };
                s.push(kid);
            }
            todo.extend(parts.into_iter().zip(sub).rev());
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
                    return Err(crate::bug(
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
            _ => Err(crate::bug(
                "called something that is not a function",
                &format!("a word tagged {} is not a closure", w.tag),
            )),
        }
    }

    /// The tuple or atom data word `w` is, for a structural pattern; `None` for any other word.
    /// The parts of an entry of the table are entered the first time.
    fn shape(&mut self, w: Word) -> Result<Option<Shape<'_>>, String> {
        let (atom, len, holder) = match w.tag {
            Word::CELL => {
                let holder = Holder::Cell(w.index());
                match obj_in(&self.cells, w)? {
                    Some(Obj::Tuple(xs)) => (None, xs.len(), holder),
                    Some(Obj::Atom { name, fields, args }) => {
                        (Some((&**name, &**fields)), args.len(), holder)
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
                    Value::Tuple(xs) => (None, xs.len(), holder),
                    Value::Atom(a) => (Some((&*a.name, &*a.fields)), a.args.len(), holder),
                    _ => unreachable!("checked a tuple or an atom"),
                }
            }
            _ => return Ok(None),
        };
        Ok(Some(Shape { atom, len, holder }))
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
                    Some(Obj::Data(v)) => v == l,
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
                                && a.args.len() == args.len() =>
                        {
                            todo.extend(args.iter().copied().zip(a.args.iter()));
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
                Some(Shape {
                    atom: Some((n, fields)),
                    len,
                    holder,
                }) if n == &**name && fields.is_empty() && len == ps.len() => {
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
    crate::bug(
        what,
        &format!("the heap's cell {i} was {did} after it was freed"),
    )
}

/// The message for a function read where a data value was expected.
fn closure_as_data() -> String {
    crate::bug(
        "treated a function as a data value such as a number, a string, a tuple or a family",
        "a closure cell was read as data",
    )
}

/// The message for a word that holds no value read as a data value.
fn not_data(tag: i64) -> String {
    crate::bug(
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
        let w = h.alloc(Obj::Tuple(vec![s, s]));
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
        let t = h.alloc(Obj::Tuple(vec![k, Word::int(2)]));
        h.inc(t).unwrap();
        let (paths, end) = one_path(&[0, 1]);
        h.release(t, &paths, &[end]).unwrap();
        assert_eq!((h.stats.increments, h.stats.decrements), (1, 1));
        assert_eq!(h.live(), 1);
    }

    #[test]
    fn a_path_into_a_scalar_is_an_error() {
        let mut h = Heap::new();
        let t = h.alloc(Obj::Tuple(vec![Word::int(1)]));
        h.inc(t).unwrap();
        let (paths, end) = one_path(&[0, 0]);
        assert_eq!(
            h.release(t, &paths, &[end]).unwrap_err(),
            crate::bug(
                "kept a part of a value that has no parts",
                "a word tagged 0 has no parts"
            )
        );
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
        h.cells[0].generation = GENERATIONS - 1;
        let last = Word::cell(0, GENERATIONS - 1);
        h.dec(last).unwrap();
        let next = h.alloc(Obj::Str("c".into()));
        assert_eq!((next.index(), next.generation()), (1, 0));
        assert_eq!(h.dec(last).unwrap_err(), freed(Freed::Dropped, 0));
    }
}
