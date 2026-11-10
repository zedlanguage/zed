//! The canonical serialization. Every node is a tag byte followed by its fields; a sequence
//! is its length then its items, a string its length in bytes then its UTF-8, and lengths
//! and integers are little-endian 64-bit words. An exact number past `i64` is its sign as a
//! tag, then the limbs of its numerator, and of a rational its denominator, in lowest terms.
//! Each tag fixes the fields that follow, so the encoding is self-delimiting and two different
//! normal forms never share an encoding.
//!
//! Binders are canonical by then, so a binder is written by its count alone (a lambda's
//! parameters, a pattern's `Bind`), and a bound variable by its level.

use num_bigint::{BigUint, Sign};
use zed_kernel::num::{Rat, TooLarge};
use zed_kernel::term::{Evidence, FixKind, Grade, GuardPos, Pattern, Term, Witness};
use zed_kernel::value::Value;

use super::binders::level_of;
use super::def::Def;
use super::domain::Domain;
use zedc_base::address::ContentAddress;
use zedc_int::int::Num;
use zedc_lattice::interval::End;
use zedc_lattice::lattice::Congruence;

type Refs<'a> = &'a dyn Fn(&str) -> Option<ContentAddress>;

struct Out<'a> {
    bytes: Vec<u8>,
    refs: Refs<'a>,
    /// The first refusal of the memory for a number or for the bytes, after which the bytes
    /// are not used.
    refused: Option<TooLarge>,
}

impl Out<'_> {
    /// Appends `bytes` once the system gives the memory the vector grows to; a refusal is kept
    /// and nothing more written.
    fn put(&mut self, bytes: &[u8]) {
        if self.refused.is_some() {
            return;
        }
        let (len, cap) = (self.bytes.len(), self.bytes.capacity());
        if cap - len < bytes.len() && self.bytes.try_reserve(bytes.len()).is_err() {
            // What `Vec` asks to grow: twice its capacity, or what the bytes need if more.
            let ask = (2 * cap).max(len + bytes.len());
            self.refused = Some(TooLarge {
                bits: BigUint::from(ask) << 3u32,
            });
            return;
        }
        self.bytes.extend_from_slice(bytes);
    }

    fn tag(&mut self, t: u8) {
        self.put(&[t]);
    }

    fn word(&mut self, n: u64) {
        self.put(&n.to_le_bytes());
    }

    fn str(&mut self, s: &str) {
        self.word(s.len() as u64);
        self.put(s.as_bytes());
    }

    /// A number's magnitude: its count of 64-bit limbs, then the limbs, least significant
    /// first, each a word. Linear in its bits, where decimal digits cost more than linear time
    /// to convert.
    // Complexity tradeoff: as at `zir::binary`'s `magnitude` (COMPLEXITY.md Z26): decimal
    // digits, about n^1.5 in the bits n, replaced by the 64-bit limbs, O(n); the kernel address
    // changed with the form. Test
    // `l01_32_canonical_zir::wide_constants::addressing_a_wide_constant_is_linear_in_its_bits`.
    fn magnitude(&mut self, m: &BigUint) {
        self.word(m.iter_u64_digits().len() as u64);
        m.iter_u64_digits().for_each(|d| self.word(d));
    }

    /// An exact number: its sign as a tag, then the magnitude of its numerator, and of a
    /// rational its denominator. Both are built, and the bytes for them reserved, only after
    /// the system gives the memory; a refusal is kept and nothing more of the number written.
    fn number(&mut self, r: &Rat, rational: bool) {
        if self.refused.is_some() {
            return;
        }
        let parts = r.built_parts().and_then(|(num, den)| {
            let limbs = num.iter_u64_digits().len() + den.iter_u64_digits().len();
            let bytes = 8 * (limbs + 2);
            self.bytes.try_reserve(bytes).map_err(|_| TooLarge {
                bits: BigUint::from(bytes) << 3u32,
            })?;
            Ok((num, den))
        });
        match parts {
            Ok((num, den)) => {
                self.tag(u8::from(r.is_negative()));
                self.magnitude(&num);
                if rational {
                    self.magnitude(&den);
                }
            }
            Err(e) => self.refused = Some(e),
        }
    }

    /// An integer of an interval end or a class past `i64`: its sign as a tag, then its
    /// magnitude, as [`Out::number`] writes a numerator. A kept value is written out only after
    /// the system gives the memory ([`Num::built`]); a refusal is kept and nothing more of the
    /// integer written.
    fn int(&mut self, v: &Num) {
        if self.refused.is_some() {
            return;
        }
        match v.built() {
            Ok(b) => {
                self.tag(u8::from(b.sign() == Sign::Minus));
                self.magnitude(b.magnitude());
            }
            Err(e) => self.refused = Some(e),
        }
    }

    /// An endpoint: an integer in `i64` is a word, as an `int` value is; one past it is its
    /// sign and limbs ([`Out::int`]) under a tag of its own.
    fn end(&mut self, e: &End) {
        match e {
            End::NegInf => self.tag(0),
            End::Fin(v) => match v.to_i64() {
                Some(v) => {
                    self.tag(1);
                    self.word(v as u64);
                }
                None => {
                    self.tag(3);
                    self.int(v);
                }
            },
            End::PosInf => self.tag(2),
        }
    }

    fn domain(&mut self, d: &Domain) {
        self.word(d.ints.len() as u64);
        for (lo, hi) in d.ints.pieces() {
            self.end(lo);
            self.end(hi);
        }
        // A class whose modulus and residue fit in `i64` is two words; one past it is their
        // signs and limbs under a tag of its own, as at `end`.
        match &d.class {
            Congruence::Bottom => self.tag(0),
            Congruence::Class { modulus, residue } => match (modulus.to_i64(), residue.to_i64()) {
                (Some(m), Some(r)) => {
                    self.tag(1);
                    self.word(m as u64);
                    self.word(r as u64);
                }
                _ => {
                    self.tag(2);
                    self.int(modulus);
                    self.int(residue);
                }
            },
        }
    }

    fn value(&mut self, v: &Value) {
        self.write(Job::Value(v));
    }

    fn term(&mut self, t: &Term) {
        self.write(Job::Term(t));
    }

    /// Writes `root`. What a node writes after a node inside it waits on a heap stack, in the
    /// reverse of the order it is written in, so a deep term or value does not grow the
    /// thread's stack and the bytes come out as a recursive walk writes them.
    fn write(&mut self, root: Job<'_>) {
        let mut todo = vec![root];
        while let Some(job) = todo.pop() {
            match job {
                Job::Tag(t) => self.tag(t),
                Job::Word(n) => self.word(n),
                Job::Str(s) => self.str(s),
                Job::Evidence(ev) => self.evidence(ev),
                Job::Value(v) => self.value_head(v, &mut todo),
                Job::Pattern(p) => self.pattern_head(p, &mut todo),
                Job::Term(t) => self.term_head(t, &mut todo),
            }
        }
    }

    /// Writes the length of `items`, and puts the items on `todo` to write next, in order.
    fn seq<'t, T>(&mut self, items: &'t [T], job: fn(&'t T) -> Job<'t>, todo: &mut Vec<Job<'t>>) {
        self.word(items.len() as u64);
        todo.extend(items.iter().rev().map(job));
    }

    /// Writes the start of `v`, and puts what follows on `todo`.
    fn value_head<'t>(&mut self, v: &'t Value, todo: &mut Vec<Job<'t>>) {
        match v {
            Value::Bool(b) => {
                self.tag(0);
                self.tag(u8::from(*b));
            }
            Value::Int(n) => {
                self.tag(1);
                self.word(*n as u64);
            }
            Value::Float(x) => {
                self.tag(2);
                self.word(x.get().to_bits());
            }
            Value::Str(s) => {
                self.tag(3);
                // The text is written block by block, as `str` writes one block.
                self.word(s.len() as u64);
                s.chunks().for_each(|c| self.put(c.as_bytes()));
            }
            Value::Atom(a) if a.fields.is_empty() => {
                self.tag(4);
                self.str(&a.name);
                self.seq(&a.args, Job::Value, todo);
            }
            Value::Atom(a) => {
                self.tag(10);
                self.str(&a.name);
                self.word(a.fields.len() as u64);
                a.fields.iter().for_each(|f| self.str(f));
                self.seq(&a.args, Job::Value, todo);
            }
            Value::Big(n) => {
                self.tag(8);
                self.number(n, false);
            }
            Value::Rat(r) => {
                self.tag(9);
                self.number(r, true);
            }
            Value::Tuple(vs) => {
                self.tag(5);
                self.seq(vs, Job::Value, todo);
            }
            Value::Path(vs) => {
                self.tag(6);
                self.seq(vs, Job::Value, todo);
            }
            Value::Family(f) => {
                self.tag(7);
                self.word(f.len() as u64);
                let start = todo.len();
                for (k, v) in f.iter() {
                    todo.extend([Job::Value(k), Job::Value(v)]);
                }
                todo[start..].reverse();
            }
        }
    }

    /// Writes the start of `p`, and puts what follows on `todo`.
    fn pattern_head<'t>(&mut self, p: &'t Pattern, todo: &mut Vec<Job<'t>>) {
        match p {
            Pattern::Wild => self.tag(0),
            Pattern::Bind(_) => self.tag(1),
            Pattern::Lit(v) => {
                self.tag(2);
                todo.push(Job::Value(v));
            }
            Pattern::Atom(name, ps) => {
                self.tag(3);
                self.str(name);
                self.seq(ps, Job::Pattern, todo);
            }
            Pattern::Tuple(ps) => {
                self.tag(4);
                self.seq(ps, Job::Pattern, todo);
            }
            Pattern::AnyAtom => self.tag(5),
            Pattern::Is(t) => {
                self.tag(7);
                self.str(&t.to_string());
            }
            Pattern::Fields(name, fs) => {
                self.tag(6);
                self.str(name);
                self.word(fs.len() as u64);
                for (f, p) in fs.iter().rev() {
                    todo.extend([Job::Pattern(p), Job::Str(f)]);
                }
            }
        }
    }

    /// An evidence record, its properties in name order, each with its grade.
    fn evidence(&mut self, ev: &Evidence) {
        self.word(ev.len() as u64);
        for (property, grade) in ev {
            self.str(property);
            self.tag(match grade {
                Grade::Axiom => 0,
                Grade::CheckedExhaustive => 1,
                Grade::Proved => 2,
                Grade::Bounded => 3,
                Grade::Obligated => 4,
                Grade::Assumed => 5,
            });
        }
    }

    /// Writes the start of `t`, and puts what follows on `todo`.
    fn term_head<'t>(&mut self, t: &'t Term, todo: &mut Vec<Job<'t>>) {
        match t {
            Term::Lit(v) => {
                self.tag(1);
                todo.push(Job::Value(v));
            }
            Term::Var(x) => match level_of(x) {
                Some(level) => {
                    self.tag(2);
                    self.word(level as u64);
                }
                None => match (self.refs)(x) {
                    Some(a) => {
                        self.tag(3);
                        self.put(&a.0);
                    }
                    None => {
                        self.tag(4);
                        self.str(x);
                    }
                },
            },
            Term::Lam(params, body) => {
                self.tag(5);
                self.word(params.len() as u64);
                todo.push(Job::Term(body));
            }
            Term::App(f, args) => {
                self.tag(6);
                todo.extend(args.iter().rev().map(Job::Term));
                todo.extend([Job::Word(args.len() as u64), Job::Term(f)]);
            }
            Term::Prim(p, args) => {
                self.tag(7);
                self.word(p.code());
                self.seq(args, Job::Term, todo);
            }
            Term::PrimFn(p) => {
                self.tag(8);
                self.word(p.code());
            }
            Term::Let(_, e, body) => {
                self.tag(9);
                todo.extend([Job::Term(body), Job::Term(e)]);
            }
            Term::If(c, a, b) => {
                self.tag(10);
                todo.extend([Job::Term(b), Job::Term(a), Job::Term(c)]);
            }
            Term::Match(e, arms) => {
                self.tag(11);
                for (p, arm) in arms.iter().rev() {
                    todo.extend([Job::Term(arm), Job::Pattern(p)]);
                }
                todo.extend([Job::Word(arms.len() as u64), Job::Term(e)]);
            }
            Term::Fam { domain, body, .. } => {
                self.tag(12);
                todo.extend([Job::Term(body), Job::Term(domain)]);
            }
            Term::Reindex {
                family,
                kf,
                vf,
                witness,
            } => {
                self.tag(13);
                match witness {
                    Witness::Residue => todo.push(Job::Tag(0)),
                    Witness::Catalog(name) => todo.extend([Job::Str(name), Job::Tag(1)]),
                }
                todo.extend([Job::Term(vf), Job::Term(kf), Job::Term(family)]);
            }
            Term::Discard { family, sel } => {
                self.tag(14);
                todo.extend([Job::Term(sel), Job::Term(family)]);
            }
            Term::Fold {
                family,
                op,
                identity,
                depth,
                ev,
            } => {
                self.tag(15);
                todo.extend([Job::Evidence(ev), Job::Word(*depth as u64)]);
                match identity {
                    None => todo.push(Job::Tag(0)),
                    Some(i) => todo.extend([Job::Term(i), Job::Tag(1)]),
                }
                todo.extend([Job::Term(op), Job::Term(family)]);
            }
            Term::Fix {
                init,
                step,
                kind,
                ev,
                ..
            } => {
                self.tag(16);
                todo.push(Job::Evidence(ev));
                match kind {
                    FixKind::Lattice { join } => todo.extend([Job::Term(join), Job::Tag(0)]),
                    FixKind::Definedness => todo.push(Job::Tag(1)),
                }
                todo.extend([Job::Term(step), Job::Term(init)]);
            }
            Term::Gen {
                init,
                step,
                guard,
                pos,
            } => {
                self.tag(17);
                let pos = match pos {
                    GuardPos::Before => 0,
                    GuardPos::After => 1,
                };
                todo.extend([
                    Job::Tag(pos),
                    Job::Term(guard),
                    Job::Term(step),
                    Job::Term(init),
                ]);
            }
            Term::Read(port) => {
                self.tag(18);
                self.str(port);
            }
            Term::Push(port, v) => {
                self.tag(19);
                self.str(port);
                todo.push(Job::Term(v));
            }
        }
    }
}

/// A piece of the serialization still to write, on [`Out::write`]'s heap stack.
#[derive(Clone, Copy)]
enum Job<'t> {
    Term(&'t Term),
    Value(&'t Value),
    Pattern(&'t Pattern),
    Tag(u8),
    Word(u64),
    Str(&'t str),
    Evidence(&'t Evidence),
}

/// The serialization of a definition in normal form, or [`TooLarge`] when the system refuses
/// the memory to build or write one of its exact numbers ([`Rat::built_parts`], [`Num::built`])
/// or to grow the bytes.
pub fn def(d: &Def, refs: Refs<'_>) -> Result<Vec<u8>, TooLarge> {
    let mut out = Out {
        bytes: Vec::new(),
        refs,
        refused: None,
    };
    out.str(&d.name);
    match &d.domain {
        None => out.tag(0),
        Some(dom) => {
            out.tag(1);
            out.domain(dom);
        }
    }
    out.word(d.facets.len() as u64);
    for f in &d.facets {
        out.tag(u8::from(f.hint));
        out.str(&f.kind);
        out.value(&f.value);
    }
    out.term(&d.body);
    match out.refused {
        None => Ok(out.bytes),
        Some(e) => Err(e),
    }
}
