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
//! string a cell holding a [`Rope`], and a big integer, a rational, a keypath and a family a
//! cell holding the kernel value. A cell's count is the number of references to it; at 0 it
//! is freed, its parts dropped, and a later use of it is an error.

use std::sync::Arc;

use zed_kernel::term::Pattern;
use zed_kernel::value::{Atom, Value};

use crate::rope::Rope;

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
    /// A heap cell; the payload is its index.
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
}

/// What a cell holds.
#[derive(Clone, Debug)]
pub enum Obj {
    /// A string.
    Str(Rope),
    /// A non-empty tuple.
    Tuple(Vec<Word>),
    /// An atom with a payload, its parts in the order of [`Atom::args`].
    Atom {
        /// The atom's name.
        name: Arc<str>,
        /// The field names of a struct payload, sorted; empty for a tuple payload.
        fields: Vec<Arc<str>>,
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

/// A heap cell: its count, its contents until it is freed, and whether it was ever shared.
#[derive(Debug)]
struct Cell {
    count: u32,
    obj: Option<Obj>,
    shared: bool,
}

/// The counts of one run, the same measures as the counting machine of step L1.34 keeps,
/// and the bytes ropes copied.
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
    /// The bytes copied flattening ropes.
    pub copied: u64,
}

/// The structure of a data word, for matching.
enum Parts {
    Tuple(Vec<Word>),
    Atom(Arc<str>, Vec<Arc<str>>, Vec<Word>),
    Other,
}

/// The heap of one run.
#[derive(Debug, Default)]
pub struct Heap {
    cells: Vec<Cell>,
    vals: Vec<Value>,
    /// The counts so far.
    pub stats: Stats,
    live: u64,
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

    /// The word of `v`, uncounted: a scalar, or an entry of the table.
    pub fn uncounted(&mut self, v: Value) -> Word {
        if let Some(w) = Word::scalar(&v) {
            return w;
        }
        self.vals.push(v);
        Word {
            tag: Word::VAL,
            bits: self.vals.len() as i64 - 1,
        }
    }

    /// The uncounted value of word `w`, tagged [`Word::VAL`].
    pub fn value_ref(&self, w: Word) -> &Value {
        &self.vals[w.bits as usize]
    }

    /// A new cell holding `obj`, with count 1.
    pub fn alloc(&mut self, obj: Obj) -> Word {
        self.cells.push(Cell {
            count: 1,
            obj: Some(obj),
            shared: false,
        });
        self.stats.allocations += 1;
        self.live += 1;
        self.stats.peak = self.stats.peak.max(self.live);
        Word {
            tag: Word::CELL,
            bits: self.cells.len() as i64 - 1,
        }
    }

    /// A fresh word for `v`, owned: its cells allocated, each part of a tuple or an atom its
    /// own, as the counting machine allocates a value the kernel returns.
    pub fn fresh(&mut self, v: &Value) -> Word {
        if let Some(w) = Word::scalar(v) {
            return w;
        }
        match v {
            Value::Tuple(xs) if xs.is_empty() => self.uncounted(v.clone()),
            Value::Atom(a) if a.args.is_empty() => self.uncounted(v.clone()),
            Value::Tuple(xs) => {
                let parts = xs.iter().map(|x| self.fresh(x)).collect();
                self.alloc(Obj::Tuple(parts))
            }
            Value::Atom(a) => {
                let args = a.args.iter().map(|x| self.fresh(x)).collect();
                self.alloc(Obj::Atom {
                    name: a.name.clone(),
                    fields: a.fields.clone(),
                    args,
                })
            }
            Value::Str(s) => self.alloc(Obj::Str(Rope::leaf(s.clone()))),
            _ => self.alloc(Obj::Data(v.clone())),
        }
    }

    /// What live cell `w` holds; `None` for a word that is not a cell.
    pub fn obj(&self, w: Word) -> Result<Option<&Obj>, String> {
        if w.tag != Word::CELL {
            return Ok(None);
        }
        match &self.cells[w.bits as usize].obj {
            Some(o) => Ok(Some(o)),
            None => Err(format!(
                "runtime: cell {} is used after it was freed",
                w.bits
            )),
        }
    }

    /// Whether `w` is a function: a closure, a primitive or a lookup port.
    pub fn is_function(&self, w: Word) -> Result<bool, String> {
        Ok(match w.tag {
            Word::PRIM | Word::SOURCE => true,
            Word::CELL => matches!(self.obj(w)?, Some(Obj::Clo { .. })),
            _ => false,
        })
    }

    /// The kernel value of data word `w`; a string's rope is flattened.
    pub fn value(&mut self, w: Word) -> Result<Value, String> {
        Ok(match w.tag {
            Word::INT => Value::Int(w.bits),
            Word::FLOAT => Value::float(f64::from_bits(w.bits as u64)),
            Word::BOOL => Value::Bool(w.bits != 0),
            Word::VAL => self.vals[w.bits as usize].clone(),
            Word::CELL => match self.obj(w)?.cloned() {
                Some(Obj::Str(r)) => Value::Str(r.flat(&mut self.stats.copied)),
                Some(Obj::Tuple(xs)) => Value::Tuple(
                    xs.iter()
                        .map(|x| self.value(*x))
                        .collect::<Result<_, _>>()?,
                ),
                Some(Obj::Atom { name, fields, args }) => Value::Atom(Atom {
                    name,
                    fields,
                    args: args
                        .iter()
                        .map(|x| self.value(*x))
                        .collect::<Result<_, _>>()?,
                }),
                Some(Obj::Data(v)) => v,
                Some(Obj::Clo { .. }) => return Err("runtime: a closure is not data".into()),
                None => unreachable!("obj checks the cell is live"),
            },
            t => return Err(format!("runtime: a word tagged {t} is not data")),
        })
    }

    /// Adds a reference to `w`, when it is a cell.
    pub fn inc(&mut self, w: Word) {
        if w.tag != Word::CELL {
            return;
        }
        self.stats.increments += 1;
        let c = &mut self.cells[w.bits as usize];
        c.count += 1;
        if c.count == 2 && !c.shared {
            c.shared = true;
            self.stats.shared += 1;
        }
    }

    /// Drops a reference to `w`, when it is a cell, freeing it and dropping its parts at 0.
    pub fn dec(&mut self, w: Word) -> Result<(), String> {
        let mut todo = vec![w];
        while let Some(w) = todo.pop() {
            if w.tag != Word::CELL {
                continue;
            }
            self.stats.decrements += 1;
            let c = &mut self.cells[w.bits as usize];
            if c.count == 0 {
                return Err(format!(
                    "runtime: cell {} is dropped after it was freed",
                    w.bits
                ));
            }
            c.count -= 1;
            if c.count == 0 {
                let obj = c.obj.take().expect("a live cell holds its contents");
                self.stats.frees += 1;
                self.live -= 1;
                // In reverse, so the parts are dropped first to last.
                todo.extend(obj.take_parts().into_iter().rev());
            }
        }
        Ok(())
    }

    /// The fused release of step L1.34 of scrutinee `w`, keeping the parts at the paths
    /// `kept`: a cell with count 1 is freed without a count write, the kept parts' references
    /// moving out of it and the others dropped; a shared cell gives each kept part a
    /// reference and loses one.
    pub fn release(&mut self, w: Word, kept: &[&[usize]]) -> Result<(), String> {
        if w.tag != Word::CELL || kept.iter().any(|p| p.is_empty()) {
            return Ok(());
        }
        self.obj(w)?;
        let c = &mut self.cells[w.bits as usize];
        if c.count == 1 {
            c.count = 0;
            let obj = c.obj.take().expect("checked live");
            self.stats.frees += 1;
            self.live -= 1;
            for (i, part) in obj.take_parts().into_iter().enumerate() {
                let sub: Vec<&[usize]> =
                    kept.iter().filter(|p| p[0] == i).map(|p| &p[1..]).collect();
                if sub.is_empty() {
                    self.dec(part)?;
                } else {
                    self.release(part, &sub)?;
                }
            }
        } else {
            for p in kept {
                let part = self.at(w, p)?;
                self.inc(part);
            }
            self.dec(w)?;
        }
        Ok(())
    }

    /// The part of `w` at the path of part indices `path`.
    fn at(&self, mut w: Word, path: &[usize]) -> Result<Word, String> {
        for &i in path {
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

    fn parts(&mut self, w: Word) -> Result<Parts, String> {
        Ok(match w.tag {
            Word::CELL => match self.obj(w)? {
                Some(Obj::Tuple(xs)) => Parts::Tuple(xs.clone()),
                Some(Obj::Atom { name, fields, args }) => {
                    Parts::Atom(name.clone(), fields.clone(), args.clone())
                }
                _ => Parts::Other,
            },
            Word::VAL => match self.vals[w.bits as usize].clone() {
                Value::Tuple(xs) => {
                    Parts::Tuple(xs.into_iter().map(|x| self.uncounted(x)).collect())
                }
                Value::Atom(a) => Parts::Atom(
                    a.name,
                    a.fields,
                    a.args.into_iter().map(|x| self.uncounted(x)).collect(),
                ),
                _ => Parts::Other,
            },
            _ => Parts::Other,
        })
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
        if self.is_function(w)? {
            return Ok(match p {
                Pattern::Wild => true,
                Pattern::Bind(_) => {
                    out.push((w, at.clone()));
                    true
                }
                Pattern::Is(t) => t.functions(),
                _ => false,
            });
        }
        let mut sub = |h: &mut Heap, i: usize, q: &Pattern, x: Word, out: &mut Vec<_>| {
            at.push(i);
            let m = h.matches(q, x, at, out);
            at.pop();
            m
        };
        Ok(match p {
            Pattern::Wild => true,
            Pattern::Bind(_) => {
                out.push((w, at.clone()));
                true
            }
            Pattern::Lit(l) => self.value(w)? == *l,
            Pattern::AnyAtom => matches!(self.parts(w)?, Parts::Atom(..)),
            Pattern::Is(t) => {
                let v = self.value(w)?;
                t.contains(&v)
            }
            Pattern::Atom(name, ps) => match self.parts(w)? {
                Parts::Atom(n, fields, args)
                    if n == *name && fields.is_empty() && ps.len() == args.len() =>
                {
                    for (i, (q, x)) in ps.iter().zip(args).enumerate() {
                        if !sub(self, i, q, x, out)? {
                            return Ok(false);
                        }
                    }
                    true
                }
                _ => false,
            },
            Pattern::Fields(name, fs) => match self.parts(w)? {
                Parts::Atom(n, fields, args) if n == *name && !fields.is_empty() => {
                    for (f, q) in fs {
                        let Ok(i) = fields.binary_search(f) else {
                            return Ok(false);
                        };
                        if !sub(self, i, q, args[i], out)? {
                            return Ok(false);
                        }
                    }
                    true
                }
                _ => false,
            },
            Pattern::Tuple(ps) => match self.parts(w)? {
                Parts::Tuple(xs) if xs.len() == ps.len() => {
                    for (i, (q, x)) in ps.iter().zip(xs).enumerate() {
                        if !sub(self, i, q, x, out)? {
                            return Ok(false);
                        }
                    }
                    true
                }
                _ => false,
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
        let v = Value::Tuple(vec![Value::str("a"), Value::str("b")]);
        let w = h.fresh(&v);
        assert_eq!((h.stats.allocations, h.live()), (3, 3));
        assert_eq!(h.value(w).unwrap(), v);
        h.dec(w).unwrap();
        assert_eq!((h.stats.frees, h.live()), (3, 0));
        assert!(h.value(w).is_err(), "a use after free is caught");
        assert!(h.dec(w).is_err(), "a second drop is caught");
    }

    #[test]
    fn fused_release_keeps_one_part_with_no_count_write() {
        let mut h = Heap::new();
        let w = h.fresh(&Value::Tuple(vec![Value::str("a"), Value::str("b")]));
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
}
