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

use std::collections::BTreeMap;
use std::sync::Arc;
use std::{mem, slice};

use zed_kernel::term::Pattern;
use zed_kernel::types::{Type, Universe};
use zed_kernel::value::{Atom, Items, Value};

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
        fields: Arc<[Arc<str>]>,
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
}

/// An entry of the table: an uncounted value, and where the entries of its parts start once a
/// match has read them.
#[derive(Debug)]
struct Entry {
    value: Value,
    parts: Option<usize>,
}

/// The counts of one run, the same measures as the counting machine of step L1.34 keeps,
/// and the bytes strings copied when written out.
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
    /// The bytes copied writing out a string that was a join, to compare it with a literal.
    pub copied: u64,
    /// The words [`Heap::value`] read to make kernel values: one for a word whose value it had
    /// already made.
    pub converted: u64,
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
        _ => Err(format!(
            "runtime: cell {} is used after it was freed",
            w.index()
        )),
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
                i
            }
            None => {
                self.cells.push(Cell {
                    count: 1,
                    generation: 0,
                    obj: Some(obj),
                    shared: false,
                    value: None,
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

    /// A fresh word for `v`, owned: its cells allocated, each part of a tuple or an atom its
    /// own, as the counting machine allocates a value the kernel returns. Each cell keeps its
    /// part of `v` as its kernel value, so handing it to the kernel again reads nothing.
    pub fn fresh(&mut self, v: &Value) -> Word {
        let mut stack: Vec<Making<'_>> = Vec::new();
        let mut next = v;
        loop {
            let (atom, items): (_, &[Value]) = match next {
                Value::Tuple(xs) => (None, xs),
                Value::Atom(a) => (Some(a), &a.args),
                _ => (None, &[]),
            };
            let mut rest = items.iter();
            if let Some(first) = rest.next() {
                stack.push(Making {
                    value: next,
                    atom,
                    rest,
                    parts: Vec::with_capacity(items.len()),
                });
                next = first;
                continue;
            }
            let mut w = self.fresh_leaf(next);
            // Each finished value is a part of the one below it on the stack.
            loop {
                let Some(top) = stack.last_mut() else {
                    return w;
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
                Some(Obj::Clo { .. }) => return Err("runtime: a closure is not data".into()),
                None => unreachable!("obj_in checks the cell is live"),
            },
            t => return Err(format!("runtime: a word tagged {t} is not data")),
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
            return Err(format!(
                "runtime: cell {} is shared after it was freed",
                w.index()
            ));
        }
        c.count = c.count.checked_add(1).ok_or_else(|| {
            format!(
                "runtime: cell {} has {} references, the most a count holds",
                w.index(),
                u32::MAX
            )
        })?;
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
            return Err(format!(
                "runtime: cell {} is dropped after it was freed",
                w.index()
            ));
        }
        c.count -= 1;
        if c.count > 0 {
            return Ok(None);
        }
        Ok(Some(self.free_cell(w.index())))
    }

    /// The fused release of step L1.34 of scrutinee `w`, keeping the parts at the paths
    /// `kept`: a cell with count 1 is freed without a count write, the kept parts' references
    /// moving out of it and the others dropped; a shared cell gives each kept part a
    /// reference and loses one.
    pub fn release(&mut self, w: Word, kept: &[&[usize]]) -> Result<(), String> {
        let mut todo = Vec::new();
        self.release_one(w, kept, &mut todo)?;
        // An empty list of paths on the stack is a part nothing keeps.
        while let Some((part, sub)) = todo.pop() {
            if sub.is_empty() {
                self.dec(part)?;
            } else {
                self.release_one(part, &sub, &mut todo)?;
            }
        }
        Ok(())
    }

    /// One cell of a fused release: the parts of a cell it frees go on `todo`, the first on top,
    /// each with the paths kept in it.
    fn release_one<'k>(
        &mut self,
        w: Word,
        kept: &[&'k [usize]],
        todo: &mut Vec<(Word, Vec<&'k [usize]>)>,
    ) -> Result<(), String> {
        if w.tag != Word::CELL || kept.iter().any(|p| p.is_empty()) {
            return Ok(());
        }
        self.obj(w)?;
        let c = &mut self.cells[w.index()];
        if c.count == 1 {
            c.count = 0;
            let parts = self.free_cell(w.index()).take_parts();
            // Each kept path goes to the part it starts at, in one step.
            let mut sub = vec![Vec::new(); parts.len()];
            for p in kept {
                let Some(s) = sub.get_mut(p[0]) else {
                    return Err(format!(
                        "runtime: a kept path reads part {} of a cell of {} parts",
                        p[0],
                        parts.len()
                    ));
                };
                s.push(&p[1..]);
            }
            todo.extend(parts.into_iter().zip(sub).rev());
        } else {
            for p in kept {
                let part = self.at(w, p)?;
                self.inc(part)?;
            }
            self.dec(w)?;
        }
        Ok(())
    }

    /// The part of `w` at the path of part indices `path`, or the first constant on the way
    /// there: every part of a constant is a constant, which [`Heap::inc`] does not count.
    fn at(&self, mut w: Word, path: &[usize]) -> Result<Word, String> {
        for &i in path {
            if w.tag == Word::VAL {
                break;
            }
            w = match self.obj(w)? {
                Some(o) => o.parts()[i],
                None => return Err(format!("runtime: a word tagged {} has no parts", w.tag)),
            };
        }
        Ok(w)
    }

    /// Part `i` of closure `w`, borrowed: a capture.
    pub fn capture(&self, w: Word, i: usize) -> Result<Word, String> {
        match self.obj(w)? {
            Some(Obj::Clo { caps, .. }) => Ok(caps[i]),
            _ => Err(format!("runtime: a word tagged {} is not a closure", w.tag)),
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
                        Value::Str(s) if r.len() == s.len() => {
                            if !r.is_written_out() {
                                self.stats.copied += r.len() as u64;
                            }
                            r == s
                        }
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
                    Some(Obj::Clo { .. }) => return Err("runtime: a closure is not data".into()),
                    None => unreachable!("obj_in checks the cell is live"),
                },
                t => return Err(format!("runtime: a word tagged {t} is not data")),
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

    /// Whether `w` matches `p`, as the kernel matches a value: on success, `out` holds each
    /// binder's word and its path of part indices inside `w`, in preorder. A function
    /// matches only `_`, a name, and `is T` for a type `T` of functions.
    pub fn matches(
        &mut self,
        p: &Pattern,
        w: Word,
        at: &mut Vec<usize>,
        out: &mut Vec<(Word, Vec<usize>)>,
    ) -> Result<bool, String> {
        let start = at.len();
        let r = self.match_all(p, w, at, out);
        at.truncate(start);
        r
    }

    /// [`Heap::matches`], leaving `at` where it stopped. Patterns nest as deep as the source
    /// writes them, so the patterns in progress are on a stack, each with its next part.
    fn match_all(
        &mut self,
        p: &Pattern,
        w: Word,
        at: &mut Vec<usize>,
        out: &mut Vec<(Word, Vec<usize>)>,
    ) -> Result<bool, String> {
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
                    at.pop();
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
                        at.push(i);
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

    /// Reads `w` against `p`, leaving any sub-patterns to [`Heap::match_all`].
    fn match_shallow<'p>(
        &mut self,
        p: &'p Pattern,
        w: Word,
        at: &[usize],
        out: &mut Vec<(Word, Vec<usize>)>,
    ) -> Result<Shallow<'p>, String> {
        let yes = |m: bool| if m { Shallow::Yes } else { Shallow::No };
        if self.is_function(w)? {
            return Ok(match p {
                Pattern::Wild => Shallow::Yes,
                Pattern::Bind(_) => {
                    out.push((w, at.to_vec()));
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
                out.push((w, at.to_vec()));
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_pair_of_strings_is_three_cells_and_frees_whole() {
        let mut h = Heap::new();
        let v = Value::tuple(vec![Value::str("a"), Value::str("b")]);
        let w = h.fresh(&v);
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
        let s = h.fresh(&Value::str("a"));
        h.inc(s).unwrap();
        h.dec(s).unwrap();
        assert_eq!((h.stats.decrements, h.live()), (1, 1));
        h.dec(s).unwrap();
        assert_eq!((h.stats.decrements, h.live()), (2, 0));
        assert_eq!(h.todo.capacity(), 0, "no stack was needed");
        // A nest of tuples: the stack grows once and is kept for the next free.
        let v = Value::tuple(vec![Value::tuple(vec![Value::str("a")]), Value::str("b")]);
        let w = h.fresh(&v);
        h.dec(w).unwrap();
        assert_eq!(h.live(), 0);
        let cap = h.todo.capacity();
        assert!(cap > 0 && h.todo.is_empty());
        let w = h.fresh(&v);
        h.dec(w).unwrap();
        assert_eq!((h.live(), h.todo.capacity()), (0, cap));
    }

    #[test]
    fn a_drop_after_a_free_inside_a_nest_is_an_error_and_the_next_drop_starts_clean() {
        let mut h = Heap::new();
        let s = h.fresh(&Value::str("a"));
        let w = h.alloc(Obj::Tuple(vec![s, s]));
        assert_eq!(
            h.dec(w).unwrap_err(),
            format!("runtime: cell {} is dropped after it was freed", s.bits)
        );
        assert!(h.todo.is_empty());
        let w = h.fresh(&Value::tuple(vec![Value::str("b")]));
        h.dec(w).unwrap();
        assert_eq!(h.live(), 0);
    }

    #[test]
    fn fused_release_keeps_one_part_with_no_count_write() {
        let mut h = Heap::new();
        let w = h.fresh(&Value::tuple(vec![Value::str("a"), Value::str("b")]));
        let mut out = Vec::new();
        let p = Pattern::Tuple(vec![Pattern::Bind("x".into()), Pattern::Wild]);
        assert!(h.matches(&p, w, &mut Vec::new(), &mut out).unwrap());
        assert_eq!(out[0].1, vec![0]);
        h.release(w, &[&[0]]).unwrap();
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
        h.release(t, &[&[0, 1]]).unwrap();
        assert_eq!((h.stats.increments, h.stats.decrements), (1, 1));
        assert_eq!(h.live(), 1);
    }

    #[test]
    fn a_path_into_a_scalar_is_an_error() {
        let mut h = Heap::new();
        let t = h.alloc(Obj::Tuple(vec![Word::int(1)]));
        h.inc(t).unwrap();
        assert_eq!(
            h.release(t, &[&[0, 0]]).unwrap_err(),
            "runtime: a word tagged 0 has no parts"
        );
    }

    #[test]
    fn constants_match_without_cells() {
        let mut h = Heap::new();
        let w = h.uncounted(Value::atom_with("some", vec![Value::Int(3)]));
        let mut out = Vec::new();
        let p = Pattern::Atom("some".into(), vec![Pattern::Bind("n".into())]);
        assert!(h.matches(&p, w, &mut Vec::new(), &mut out).unwrap());
        assert_eq!(out[0].0, Word::int(3));
        let q = Pattern::Atom("none".into(), vec![]);
        assert!(!h.matches(&q, w, &mut Vec::new(), &mut Vec::new()).unwrap());
        assert_eq!(h.stats.allocations, 0);
    }

    #[test]
    fn a_count_at_its_most_is_an_error_at_the_inc_itself() {
        let mut h = Heap::new();
        let w = h.alloc(Obj::Str("a".into()));
        h.cells[0].count = u32::MAX;
        let full = "runtime: cell 0 has 4294967295 references, the most a count holds";
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
        assert_eq!(
            h.dec(last).unwrap_err(),
            "runtime: cell 0 is dropped after it was freed"
        );
    }
}
