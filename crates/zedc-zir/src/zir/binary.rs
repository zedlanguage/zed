//! The binary form of ZIR: what a build caches and the backends read.
//!
//! It begins with the four bytes `ZIR\0` (`ZIRs` for a stripped module, [`super::strip`]) and
//! the version as a 32-bit little-endian word; the root region follows. Every count, index and
//! integer is a 64-bit little-endian word, every string a count of bytes and then its UTF-8 bytes
//! (a string value as the nodes of the tree its text is held in, each node once in the graph,
//! `W::text`), and every choice a one-byte tag. A name (of an atom, a field, a port or an evidence
//! key) is read by the rule the text form reads one by, and a pattern binder may also be one the
//! compiler makes (`text::not_a_binder`); a catalog entry and a string value are not names. A value
//! is written by its structure, a number outside the 64-bit range and a rational by their sign
//! and the 64-bit limbs of their numerator and denominator in lowest terms (not their decimal
//! digits, whose conversion costs more than linear time), a number kept with prime powers,
//! such as `2^2^100`, by the form it is kept in, its numerator, denominator and powers, with
//! no digits built ([`Rat::kept`]), and a float by its bits, so every value comes back bit for
//! bit. An
//! edge is written as its text form ([`super::text::edge`]): a type's representation is
//! private to the kernel, and its printed form is its exact, canonical description; reading
//! that text checks the names in it (a state edge's port, a facet's kind). A primitive is its
//! index in [`PRIMS`]. A decoding error names the byte offset at which it was found.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use num_bigint::{BigInt, BigUint, Sign};
use zed_kernel::num::{Rat, TooLarge};
use zed_kernel::term::{Evidence, Grade, GuardPos, Pattern, Witness};
use zed_kernel::text::{Piece, Text};
use zed_kernel::value::{Atom, Value};

use super::text::{self, PRIMS, VERSION};
use super::{Derived, Edge, Form, Node, Op, Region, RegionKind, Src};

/// The first four bytes of a full module ([`encode`]): [`decode_form`] reads them to tell a
/// full module from a stripped one ([`MAGIC_STRIPPED`]) and either from data that is no module.
/// The version follows them ([`VERSION`]). The bytes spell the format's name; they are not
/// chosen for any other property, and only the two must differ.
const MAGIC: &[u8; 4] = b"ZIR\0";

/// The first four bytes of a stripped module ([`encode_as_stripped`]).
const MAGIC_STRIPPED: &[u8; 4] = b"ZIRs";

/// The one NaN word the form writes: the quiet NaN with a zero payload. Rust does not fix the
/// bits of `f64::NAN`, so the form fixes them itself.
pub const NAN_BITS: u64 = 0x7ff8_0000_0000_0000;

/// The one `f32` NaN word the form writes, as [`NAN_BITS`] is for `f64`.
pub const NAN_BITS_F32: u32 = 0x7fc0_0000;

const KINDS: [RegionKind; 5] = [
    RegionKind::Function,
    RegionKind::Match,
    RegionKind::Loop,
    RegionKind::Rec,
    RegionKind::Port,
];

const GRADES: [Grade; 6] = [
    Grade::Axiom,
    Grade::CheckedExhaustive,
    Grade::Proved,
    Grade::Bounded,
    Grade::Obligated,
    Grade::Assumed,
];

const DERIVED: [Derived; 4] = [
    Derived::Group,
    Derived::OrderedValues,
    Derived::Scan,
    Derived::Join,
];

fn index<T: PartialEq>(all: &[T], x: &T) -> u8 {
    all.iter()
        .position(|y| y == x)
        .expect("every case is listed") as u8
}

// ---------------------------------------------------------------------------------------------
// Writing

/// The binary form of the graph rooted at `root`, or [`TooLarge`] when the system refuses the
/// memory to build or write one of its exact numbers ([`Rat::built_parts`]), or to grow the
/// bytes written.
pub fn encode(root: &Region) -> Result<Vec<u8>, TooLarge> {
    encode_as(MAGIC, root)
}

/// The binary form of `stripped`, a graph already stripped, which starts `ZIRs` in place of
/// `ZIR\0`, so that [`decode_form`] reads it back as stripped and [`decode`] refuses it. The
/// stripping module calls it (`strip::encode_stripped`), so that this module does not import
/// that one. [`TooLarge`] as at [`encode`].
pub(super) fn encode_as_stripped(stripped: &Region) -> Result<Vec<u8>, TooLarge> {
    encode_as(MAGIC_STRIPPED, stripped)
}

fn encode_as(magic: &[u8; 4], root: &Region) -> Result<Vec<u8>, TooLarge> {
    let mut w = W(magic.to_vec(), None, HashMap::new(), None);
    w.0.extend_from_slice(&VERSION.to_le_bytes());
    w.region(root);
    match w.1 {
        None => Ok(w.0),
        Some(e) => Err(e),
    }
}

/// A string as [`encode_keyed`] writes it: its length in bytes, its [`Text::poly_hash`], and
/// the text.
pub type Held = (u64, u64, Text);

/// The binary form of the graph rooted at `root` but for its strings, each written as its
/// length and [`Text::poly_hash`], two words, so that equal strings held in different trees
/// are written alike; and those strings in the order written. The bytes with the strings
/// decide the graph; the bytes alone decide it up to the strings, whose hashes can collide.
/// [`TooLarge`] as at [`encode`]. The canonicalizer's keys hash these bytes
/// ([`super::canon::node_key`]), and its shapes compare them with the strings' numbers
/// ([`super::canon::Strings`]).
pub fn encode_keyed(root: &Region) -> Result<(Vec<u8>, Vec<Held>), TooLarge> {
    let mut w = W(MAGIC.to_vec(), None, HashMap::new(), Some(Keyed::default()));
    w.0.extend_from_slice(&VERSION.to_le_bytes());
    w.region(root);
    match (w.1, w.3) {
        (None, Some(k)) => Ok((w.0, k.held)),
        (Some(e), _) => Err(e),
        (None, None) => unreachable!("made keyed above"),
    }
}

/// The strings a keyed writer wrote, in order, and the length and hash of each text written,
/// by its id, so that a text written twice is hashed once.
#[derive(Default)]
struct Keyed {
    held: Vec<Held>,
    memo: HashMap<usize, (u64, u64)>,
}

/// The bytes written, the first refusal of the memory for them, after which the bytes are
/// not used, the index of each node of a string's text written, by its id (`W::text`), and in
/// a keyed writer ([`encode_keyed`]) the strings written.
struct W(
    Vec<u8>,
    Option<TooLarge>,
    HashMap<usize, u64>,
    Option<Keyed>,
);

/// A writer of bytes that keeps the first refusal of memory, after which it writes nothing:
/// the binary form here ([`W`]) and the content address's serialization
/// (`canon::serial`'s `Out`), which wrote the same bytes for a word, a string, a magnitude,
/// an exact number and a number kept with prime powers with two copies of the code before
/// DRY-misc-A5 (REPORT-dryA5 row 15). Each form keeps its own tags, which differ on purpose:
/// the tags are part of what each form's readers and addresses fix.
pub(crate) trait ByteOut {
    /// The bytes written and the first refusal.
    fn sink(&mut self) -> (&mut Vec<u8>, &mut Option<TooLarge>);

    /// `bytes` at the end, once the system gives the memory to grow the bytes written for them;
    /// a refusal is kept, naming the capacity the growth asked, and nothing more is written.
    /// So a write after a wide number or a long string, which doubles the bytes written so far,
    /// asks for that memory first, as the number and the string did.
    fn put(&mut self, bytes: &[u8]) {
        let (out, refused) = self.sink();
        if refused.is_some() {
            return;
        }
        let (len, cap) = (out.len(), out.capacity());
        if cap - len < bytes.len() && out.try_reserve(bytes.len()).is_err() {
            // What `Vec` asks to grow: twice its capacity, or what the bytes need if more.
            let ask = (2 * cap).max(len + bytes.len());
            *refused = Some(TooLarge::of_bytes(ask));
            return;
        }
        out.extend_from_slice(bytes);
    }

    fn tag(&mut self, t: u8) {
        self.put(&[t]);
    }

    /// `n` as a little-endian 64-bit word.
    fn word(&mut self, n: u64) {
        self.put(&n.to_le_bytes());
    }

    /// `s`: its length in bytes as a word, then its UTF-8 bytes.
    fn str(&mut self, s: &str) {
        self.word(s.len() as u64);
        self.put(s.as_bytes());
    }

    /// A number's magnitude: its count of 64-bit limbs, then the limbs, least significant
    /// first, each a little-endian word. Linear in its bits, where decimal digits cost more
    /// than linear time to convert.
    // Complexity tradeoff: the form this replaced wrote a number past `i64` as its decimal
    // digits (`Rat::numer_text`, `denom_text`), about n^1.5 in its bits n by num-bigint's
    // conversion (COMPLEXITY.md Z26: 15.6 s at 2^25 bits, about 80 minutes at 2^30). Here the
    // sign and the 64-bit limbs of the numerator and denominator in lowest terms are written,
    // O(n). Tradeoffs: the bytes are not readable as a number, and the change of form changed
    // every content address (canonicalization version 3 to 4). Nothing is refused beyond the
    // memory refusal of `number`. Tests
    // `l01_32_canonical_zir::bench::wide_constants::addressing_a_wide_constant_is_linear_in_its_bits`
    // and `..._stays_linear_over_64_times_the_bits`.
    fn magnitude(&mut self, m: &BigUint) {
        self.word(m.iter_u64_digits().len() as u64);
        m.iter_u64_digits().for_each(|d| self.word(d));
    }

    /// An exact number: its sign as a tag, then the magnitude of its numerator, and of a
    /// rational its denominator. Both are built, and the bytes for them reserved, only after
    /// the system gives the memory; a refusal is kept and nothing more of the number written.
    fn number(&mut self, r: &Rat, rational: bool) {
        let (out, refused) = self.sink();
        if refused.is_some() {
            return;
        }
        let parts = r.built_parts().and_then(|(num, den)| {
            let limbs = num.iter_u64_digits().len() + den.iter_u64_digits().len();
            let bytes = 8 * (limbs + 2);
            out.try_reserve(bytes)
                .map_err(|_| TooLarge::of_bytes(bytes))?;
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
            Err(e) => *refused = Some(e),
        }
    }

    /// A number kept with prime powers ([`Rat::kept`]), in the form it is kept in: the sign of
    /// `num` as a tag, the magnitude of `num`, of a rational the magnitude of `den`, then the
    /// count of powers and each power's prime as a word and its exponent's sign and magnitude.
    /// No digits are built, so `2^2^100` is a few words.
    // Complexity tradeoff: `number` builds the digits, O(n) words for a number of n bits and a
    // refusal when the system cannot hold them, so a constant such as `2^2^100`, which staging
    // folds and a run uses only through operations that never build it (`mod`, a comparison),
    // made `zedc build` refuse a program `zedc run` runs (item ENGINE-one). Here the kept form
    // is written as it is: O(w) words for the w words of its parts, whatever the number's
    // size, and nothing is refused but the memory for those words. Tradeoff: equal numbers
    // kept in different forms (`1e3r` holds 2^3 5^3, `1000r` none) are written differently,
    // so two equal constants can get two node keys; a normal form would need the digits,
    // which is what this avoids. Their serializations differ too, which changed the address
    // of every program holding a kept power (canonicalization version 5 to 6, when the
    // address had a version). A plain number keeps its tags and its bytes. Tests
    // `l01_32_canonical_zir::wide_constants::a_kept_power_is_written_as_its_powers` and
    // `..._in_time_linear_in_its_parts`.
    fn kept(&mut self, r: &Rat, rational: bool) {
        let (num, den, pows) = r.kept();
        self.tag(u8::from(num.sign() == Sign::Minus));
        self.magnitude(num.magnitude());
        if rational {
            self.magnitude(den.magnitude());
        }
        self.word(pows.len() as u64);
        for (p, e) in pows {
            self.word(*p);
            self.tag(u8::from(e.sign() == Sign::Minus));
            self.magnitude(e.magnitude());
        }
    }

    /// The wide atoms `(q, f)` of a number ([`Rat::wide`], plan row KEPT-power-form), after its
    /// kept form under tags 14 and 15: their count, then each base's magnitude and each
    /// exponent's sign and magnitude. O(w) words for the w words of the atoms, as [`W::kept`].
    /// A number with no wide atom keeps its tags 2, 3, 12 and 13 and its bytes, so only the
    /// addresses of values holding a wide atom changed (each such value was built in full
    /// before, under tag 2 or 3).
    fn wide(&mut self, r: &Rat) {
        let wide = r.wide();
        self.word(wide.len() as u64);
        for (q, f) in wide {
            self.magnitude(q);
            self.tag(u8::from(f.sign() == Sign::Minus));
            self.magnitude(f.magnitude());
        }
    }
}

impl ByteOut for W {
    fn sink(&mut self) -> (&mut Vec<u8>, &mut Option<TooLarge>) {
        (&mut self.0, &mut self.1)
    }
}

impl W {
    /// A string value's text, as the tree it is held in: the count of its nodes not yet
    /// written in this graph, then each after the nodes it joins, a block as tag 0 and the
    /// block, a join as tag 1 and the indices of its parts in order, then the index of the text.
    /// The nodes of all strings of the graph are numbered from 0 in the order written, so a node
    /// that several parents or several strings share is written once.
    // Complexity tradeoff: the form this replaced wrote the text's bytes, O(N) for N bytes, and
    // `++` shares both parts, so a string doubled k times is 2^k bytes held in O(k) nodes;
    // staging cannot fold `s ++ s` past 2^63 bytes (its length is refused), so the build wrote
    // a 2^62-byte operand out until the memory ran out, past 60 s, where `zedc run` stops at
    // once with the length error (item BUILD-doubling-60s). Here each distinct node is written
    // once in the graph, O(m) words and hash lookups for m nodes, plus the bytes of the distinct
    // blocks; the reader shares them again, so a string used in several places is one text
    // there too, and equal by identity. Tradeoff: equal texts held in different trees are
    // written differently. The content address pays the bytes: it holds each string as one
    // block before writing (`canon::flat_strings`, ZIR-string-tree-address); the
    // canonicalizer's keys and shapes write a string by its length and hash instead and number
    // it exactly apart (`encode_keyed`, `canon::Strings`, ZIR-string-cse-tree). Nothing is
    // refused but the memory for the bytes. Tests
    // `l01_31_zir::binary_forms::a_doubled_string_is_written_as_its_tree` and
    // `l01_31_zir::bench::shared_strings`.
    fn text(&mut self, t: &Text) {
        if let Some(k) = &mut self.3 {
            let (len, hash) = *k
                .memo
                .entry(t.node_id())
                .or_insert_with(|| (t.len() as u64, t.poly_hash()));
            k.held.push((len, hash, t.clone()));
            self.word(len);
            self.word(hash);
            return;
        }
        // Postorder: the nodes in the order they are written. A node is opened once, and every
        // part of it is written before it: a part not opened before is opened above it on the
        // stack, so written first; a part opened before but not yet written would still be on
        // the stack below, an ancestor of its own parent, and nodes and their parts form no
        // cycle: a node is built from parts that exist before it, and never changed. A node's
        // id is its address, unique while the graph being written holds it.
        let mut order: Vec<&Text> = Vec::new();
        let mut opened: HashSet<usize> = HashSet::new();
        let mut todo: Vec<(&Text, bool)> = vec![(t, false)];
        while let Some((u, done)) = todo.pop() {
            if done {
                order.push(u);
            } else if !self.2.contains_key(&u.node_id()) && opened.insert(u.node_id()) {
                todo.push((u, true));
                if let Piece::Parts(parts) = u.piece() {
                    todo.extend(parts.into_iter().rev().map(|p| (p, false)));
                }
            }
        }
        self.word(order.len() as u64);
        for u in order {
            match u.piece() {
                Piece::Block(b) => {
                    self.tag(0);
                    self.str(b);
                }
                Piece::Parts(parts) => {
                    self.tag(1);
                    self.word(parts.len() as u64);
                    for p in parts {
                        self.word(self.2[&p.node_id()]);
                    }
                }
            }
            let next = self.2.len() as u64;
            self.2.insert(u.node_id(), next);
        }
        self.word(self.2[&t.node_id()]);
    }

    fn many<T>(&mut self, xs: &[T], mut f: impl FnMut(&mut Self, &T)) {
        self.word(xs.len() as u64);
        for x in xs {
            f(self, x);
        }
    }

    /// Writes the graph rooted at `root` from a stack of what is left to write, in the order a
    /// recursive writer would: a region's kind, arguments and nodes, each node with its regions,
    /// and then the region's results.
    fn region(&mut self, root: &Region) {
        enum Job<'a> {
            Region(&'a Region),
            Node(&'a Node),
            Results(&'a [Src]),
        }
        let mut jobs = vec![Job::Region(root)];
        while let Some(job) = jobs.pop() {
            match job {
                Job::Region(r) => {
                    self.tag(index(&KINDS, &r.kind));
                    self.many(&r.args, Self::edge);
                    self.word(r.nodes.len() as u64);
                    jobs.push(Job::Results(&r.results));
                    jobs.extend(r.nodes.iter().rev().map(Job::Node));
                }
                Job::Node(n) => {
                    self.op(&n.op);
                    self.many(&n.inputs, Self::src);
                    self.many(&n.outputs, Self::edge);
                    self.word(n.regions.len() as u64);
                    jobs.extend(n.regions.iter().rev().map(|r| Job::Region(r)));
                }
                Job::Results(rs) => self.many(rs, Self::src),
            }
        }
    }

    fn edge(&mut self, e: &Edge) {
        self.str(&text::edge(e));
    }

    fn src(&mut self, s: &Src) {
        match s {
            Src::Arg(i) => {
                self.tag(0);
                self.word(*i as u64);
            }
            Src::Out(k, p) => {
                self.tag(1);
                self.word(*k as u64);
                self.word(*p as u64);
            }
            Src::Const(v) => {
                self.tag(2);
                self.value(v);
            }
        }
    }

    /// Writes `v` from a stack of the values left to write, in the order a recursive writer
    /// would: values nest as deep as the program (step T2-mid).
    fn value(&mut self, v: &Value) {
        let mut jobs = vec![v];
        while let Some(v) = jobs.pop() {
            self.value_head(v, &mut jobs);
        }
    }

    /// Writes the tag and scalars of `v`, and puts its parts on `jobs`, the first on top.
    fn value_head<'v>(&mut self, v: &'v Value, jobs: &mut Vec<&'v Value>) {
        match v {
            Value::Bool(b) => {
                self.tag(0);
                self.tag(*b as u8);
            }
            Value::Int(i) => {
                self.tag(1);
                self.word(*i as u64);
            }
            Value::Big(b) if !b.wide().is_empty() => {
                self.tag(14);
                self.kept(b, false);
                self.wide(b);
            }
            Value::Rat(r) if !r.wide().is_empty() => {
                self.tag(15);
                self.kept(r, true);
                self.wide(r);
            }
            Value::Big(b) if b.kept().2.is_empty() => {
                self.tag(2);
                self.number(b, false);
            }
            Value::Rat(r) if r.kept().2.is_empty() => {
                self.tag(3);
                self.number(r, true);
            }
            Value::Big(b) => {
                self.tag(12);
                self.kept(b, false);
            }
            Value::Rat(r) => {
                self.tag(13);
                self.kept(r, true);
            }
            Value::Float(x) => {
                self.tag(4);
                let x = x.get();
                self.word(if x.is_nan() { NAN_BITS } else { x.to_bits() });
            }
            Value::Float32(x) => {
                self.tag(11);
                let x = x.get();
                self.word(u64::from(if x.is_nan() {
                    NAN_BITS_F32
                } else {
                    x.to_bits()
                }));
            }
            Value::Str(s) => {
                self.tag(5);
                self.text(s);
            }
            // `#e()`, apart from the bare `#e` (tag 6 with no parts).
            Value::Atom(a) if !a.is_bare() && a.args().is_empty() => {
                self.tag(10);
                self.str(&a.name);
            }
            Value::Atom(a) => {
                self.tag(6);
                self.str(&a.name);
                self.many(&a.fields, |w, f| w.str(f));
                self.word(a.args().len() as u64);
                jobs.extend(a.args().iter().rev());
            }
            Value::Tuple(vs) => {
                self.tag(7);
                self.word(vs.len() as u64);
                jobs.extend(vs.iter().rev());
            }
            Value::Path(vs) => {
                self.tag(8);
                self.word(vs.len() as u64);
                jobs.extend(vs.iter().rev());
            }
            Value::Family(f) => {
                self.tag(9);
                let entries: Vec<_> = f.iter().collect();
                self.word(entries.len() as u64);
                for (k, v) in entries.into_iter().rev() {
                    jobs.push(v);
                    jobs.push(k);
                }
            }
        }
    }

    fn evidence(&mut self, ev: &Evidence) {
        let items: Vec<_> = ev.iter().collect();
        self.many(&items, |w, (k, g)| {
            w.str(k);
            w.tag(index(&GRADES, g));
        });
    }

    fn op(&mut self, op: &Op) {
        match op {
            Op::Reindex(Witness::Residue) => self.tag(0),
            Op::Reindex(Witness::Catalog(entry)) => {
                self.tag(1);
                self.str(entry);
            }
            Op::Discard => self.tag(2),
            Op::Fold {
                depth,
                identity,
                ev,
            } => {
                self.tag(3);
                self.word(*depth as u64);
                self.tag(*identity as u8);
                self.evidence(ev);
            }
            Op::Fix { lattice, ev } => {
                self.tag(4);
                self.tag(*lattice as u8);
                self.evidence(ev);
            }
            Op::Gen(pos) => {
                self.tag(5);
                self.tag(matches!(pos, GuardPos::After) as u8);
            }
            Op::Read(port) => {
                self.tag(6);
                self.str(port);
            }
            Op::Push(port) => {
                self.tag(7);
                self.str(port);
            }
            Op::Fam => self.tag(8),
            Op::Derived(d) => {
                self.tag(9);
                self.tag(index(&DERIVED, d));
            }
            Op::Prim(p) => {
                self.tag(10);
                // `PRIMS` is in the order of the codes (`Prim::ALL`), so the code is the
                // position, read in O(1) where a search of the list took up to 90 steps.
                self.tag(u8::try_from(p.code()).expect("a code below 92"));
            }
            Op::Apply => self.tag(11),
            Op::Lambda => self.tag(12),
            Op::If => self.tag(13),
            Op::Match(ps) => {
                self.tag(14);
                self.many(ps, Self::pattern);
            }
            Op::Rec => self.tag(15),
            Op::Wave => self.tag(16),
        }
    }

    /// Writes `p` from a stack of the patterns left to write, each with the field name written
    /// before it, in the order a recursive writer would: patterns nest as deep as the program
    /// (step T2-mid).
    fn pattern(&mut self, p: &Pattern) {
        let mut jobs: Vec<(Option<&str>, &Pattern)> = vec![(None, p)];
        while let Some((field, p)) = jobs.pop() {
            if let Some(k) = field {
                self.str(k);
            }
            match p {
                Pattern::Wild => self.tag(0),
                Pattern::Bind(x) => {
                    self.tag(1);
                    self.str(x);
                }
                Pattern::Lit(v) => {
                    self.tag(2);
                    self.value(v);
                }
                Pattern::Atom(name, ps) => {
                    self.tag(3);
                    self.str(name);
                    self.word(ps.len() as u64);
                    jobs.extend(ps.iter().rev().map(|q| (None, q)));
                }
                Pattern::Fields(name, fs) => {
                    self.tag(4);
                    self.str(name);
                    self.word(fs.len() as u64);
                    jobs.extend(fs.iter().rev().map(|(k, q)| (Some(&**k), q)));
                }
                Pattern::Tuple(ps) => {
                    self.tag(5);
                    self.word(ps.len() as u64);
                    jobs.extend(ps.iter().rev().map(|q| (None, q)));
                }
                Pattern::AnyAtom => self.tag(6),
                Pattern::Is(t) => {
                    self.tag(7);
                    self.str(&t.to_string());
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Reading

/// The graph encoded in `bytes`, a full module, which [`super::validate::validate`] has not
/// yet checked. A stripped module is refused, as [`super::text::parse`] refuses one;
/// [`decode_form`] reads both.
pub fn decode(bytes: &[u8]) -> Result<Region, String> {
    match decode_form(bytes)? {
        (g, Form::Full) => Ok(g),
        (_, Form::Stripped) => Err("byte 0: the data starts `ZIRs`, so the module is stripped \
                                    of its facts, and this reader reads a full module, which \
                                    starts `ZIR\\0`"
            .into()),
    }
}

/// The graph encoded in `bytes`, a full or a stripped module (`strip::encode_stripped`), and its
/// form, which its first four bytes give; as [`decode`] otherwise.
pub fn decode_form(bytes: &[u8]) -> Result<(Region, Form), String> {
    let mut r = R {
        b: bytes,
        i: 0,
        nodes: Vec::new(),
    };
    let form = match r.take(4)? {
        m if m == MAGIC => Form::Full,
        m if m == MAGIC_STRIPPED => Form::Stripped,
        _ => return Err("byte 0: the data does not start `ZIR\\0`".into()),
    };
    let v = u32::from_le_bytes(r.take(4)?.try_into().expect("four bytes"));
    if v != VERSION {
        return Err(format!(
            "byte 4: version {v}, and this compiler reads version {VERSION}"
        ));
    }
    let root = r.region()?;
    if r.i != bytes.len() {
        let n = bytes.len() - r.i;
        let what = if n == 1 {
            "1 byte follows"
        } else {
            "bytes follow"
        };
        return Err(format!("byte {}: {what} the graph, which ends here", r.i));
    }
    Ok((root, form))
}

/// A region or node whose parts are being read, with the number of nodes or regions still
/// to read.
enum Open {
    Region(Region, usize),
    Node(Node, usize),
}

struct R<'a> {
    b: &'a [u8],
    i: usize,
    /// The nodes of the strings' texts read, in order (`R::text`).
    nodes: Vec<Text>,
}

impl<'a> R<'a> {
    fn err<T>(&self, at: usize, e: impl std::fmt::Display) -> Result<T, String> {
        Err(format!("byte {at}: {e}"))
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
        if self.b.len() - self.i < n {
            return self.err(
                self.i,
                format!("the data ends, and {n} more bytes were expected"),
            );
        }
        let out = &self.b[self.i..self.i + n];
        self.i += n;
        Ok(out)
    }

    fn tag(&mut self, max: u8, what: &str) -> Result<u8, String> {
        let at = self.i;
        let t = self.take(1)?[0];
        match t <= max {
            true => Ok(t),
            false => self.err(at, format!("{t} is not a tag of {what}")),
        }
    }

    fn n(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(
            self.take(8)?.try_into().expect("eight bytes"),
        ))
    }

    /// A count or an index: no more than the bytes left, since every item takes at least one.
    fn len(&mut self) -> Result<usize, String> {
        let at = self.i;
        let n = self.n()?;
        match n <= (self.b.len() - self.i) as u64 {
            true => Ok(n as usize),
            false => self.err(at, format!("the count {n} is more than the bytes left")),
        }
    }

    /// An index or a depth, which has no bound in the data.
    fn idx(&mut self) -> Result<usize, String> {
        let at = self.i;
        let n = self.n()?;
        usize::try_from(n).or_else(|_| self.err(at, format!("the index {n} is too large")))
    }

    /// A string: a name, a string value, or an edge or a type in its text form.
    fn s(&mut self) -> Result<String, String> {
        let n = self.len()?;
        let at = self.i;
        match std::str::from_utf8(self.take(n)?) {
            Ok(s) => Ok(s.into()),
            Err(_) => self.err(at, "a string is not UTF-8"),
        }
    }

    /// A string value's text, as [`W::text`] writes it: each new node joined from the nodes
    /// read before it in the graph, so a node that several parents or strings share is read
    /// once and shared again, O(m log m) for m nodes (a join of two trees builds O(log m)
    /// nodes) plus the bytes of the blocks; then the text, one of the nodes.
    fn text(&mut self) -> Result<Text, String> {
        let count = self.len()?;
        for _ in 0..count {
            let node = match self.tag(1, "a node of a string")? {
                0 => {
                    let at = self.i;
                    let b = self.s()?;
                    if b.is_empty() {
                        return self.err(at, "an empty block of a string");
                    }
                    Text::from(b)
                }
                _ => {
                    let parts = self.len()?;
                    let mut t = Text::from("");
                    for _ in 0..parts {
                        let p = self.node()?;
                        t = match Text::join(&t, &p) {
                            Ok(t) => t,
                            Err(_) => {
                                let at = self.i - 8;
                                return self.err(at, "a string longer than a length can hold");
                            }
                        };
                    }
                    t
                }
            };
            self.nodes.push(node);
        }
        self.node()
    }

    /// The index of a node of a string's text, read before.
    fn node(&mut self) -> Result<Text, String> {
        let at = self.i;
        let i = self.idx()?;
        match self.nodes.get(i) {
            Some(t) => Ok(t.clone()),
            None => self.err(at, format!("node {i} of a string is not yet read")),
        }
    }

    /// A name (of an atom, a field, a port or an evidence key), by the rule the text form
    /// reads one by ([`text::not_a_name`]); an error points at its count.
    fn name(&mut self) -> Result<String, String> {
        self.checked(text::not_a_name)
    }

    /// A pattern binder: a name, or a binder the compiler makes ([`text::not_a_binder`]).
    fn binder(&mut self) -> Result<String, String> {
        self.checked(text::not_a_binder)
    }

    fn checked(&mut self, why_not: fn(&str) -> Option<String>) -> Result<String, String> {
        let at = self.i;
        let s = self.s()?;
        match why_not(&s) {
            None => Ok(s),
            Some(e) => self.err(at, e),
        }
    }

    fn many<T>(
        &mut self,
        mut f: impl FnMut(&mut Self) -> Result<T, String>,
    ) -> Result<Vec<T>, String> {
        let n = self.len()?;
        (0..n).map(|_| f(self)).collect()
    }

    /// Reads the graph rooted here, from a stack of the regions and nodes begun and not yet
    /// ended, in the order [`W::region`] writes it.
    fn region(&mut self) -> Result<Region, String> {
        let mut open = vec![self.region_head()?];
        loop {
            let top = open
                .last_mut()
                .expect("the loop returns when the root ends");
            match top {
                Open::Region(_, left) if *left > 0 => {
                    *left -= 1;
                    let n = Node {
                        op: self.op()?,
                        inputs: self.many(Self::src)?,
                        outputs: self.many(Self::edge)?,
                        regions: Vec::new(),
                    };
                    let left = self.len()?;
                    open.push(Open::Node(n, left));
                }
                Open::Node(_, left) if *left > 0 => {
                    *left -= 1;
                    open.push(self.region_head()?);
                }
                Open::Region(r, _) => {
                    r.results = self.many(Self::src)?;
                    let Some(Open::Region(r, _)) = open.pop() else {
                        unreachable!("the top is this region")
                    };
                    match open.last_mut() {
                        Some(Open::Node(n, _)) => n.regions.push(Arc::new(r)),
                        Some(Open::Region(..)) => unreachable!("a region lies in a node"),
                        None => return Ok(r),
                    }
                }
                Open::Node(..) => {
                    let Some(Open::Node(n, _)) = open.pop() else {
                        unreachable!("the top is this node")
                    };
                    match open.last_mut() {
                        Some(Open::Region(r, _)) => r.nodes.push(n),
                        _ => unreachable!("a node lies in a region"),
                    }
                }
            }
        }
    }

    /// The kind, arguments and number of nodes of a region, which opens it.
    fn region_head(&mut self) -> Result<Open, String> {
        let kind = KINDS[self.tag(4, "a region kind")? as usize];
        let args = self.many(Self::edge)?;
        let left = self.len()?;
        let r = Region {
            kind,
            args,
            nodes: Vec::new(),
            results: Vec::new(),
        };
        Ok(Open::Region(r, left))
    }

    fn edge(&mut self) -> Result<Edge, String> {
        let at = self.i;
        let s = self.s()?;
        text::parse_edge(&s).or_else(|e| self.err(at, format!("the edge `{s}`: {e}")))
    }

    fn src(&mut self) -> Result<Src, String> {
        Ok(match self.tag(2, "a source")? {
            0 => Src::Arg(self.idx()?),
            1 => Src::Out(self.idx()?, self.idx()?),
            _ => Src::Const(self.value()?),
        })
    }

    /// A number's sign, as a tag, and its magnitude, as [`W::magnitude`] writes it.
    fn big(&mut self) -> Result<BigInt, String> {
        let sign = match self.tag(1, "a sign")? {
            0 => Sign::Plus,
            _ => Sign::Minus,
        };
        Ok(BigInt::from_biguint(sign, self.magnitude()?))
    }

    /// A magnitude as [`W::magnitude`] writes it: its limbs in order are its little-endian
    /// bytes.
    fn magnitude(&mut self) -> Result<BigUint, String> {
        let at = self.i;
        let n = self.len()?;
        match n.checked_mul(8) {
            Some(bytes) => Ok(BigUint::from_bytes_le(self.take(bytes)?)),
            None => self.err(at, format!("the count {n} is more than the bytes left")),
        }
    }

    /// Reads a value from a stack of the tuples, paths, atoms and families begun and not yet
    /// ended, in the order [`W::value`] writes it: values nest as deep as the program (step
    /// T2-mid).
    fn value(&mut self) -> Result<Value, String> {
        let mut open: Vec<OpenValue> = Vec::new();
        loop {
            let mut got = match self.value_head()? {
                Ok(v) => Some(v),
                Err(o) => {
                    open.push(o);
                    None
                }
            };
            loop {
                let Some(top) = open.last_mut() else {
                    return Ok(got.expect("a value read"));
                };
                if let Some(v) = got.take() {
                    top.put(v);
                }
                if top.left() > 0 {
                    break;
                }
                let o = open.pop().expect("the top");
                got = Some(self.close_value(o)?);
            }
        }
    }

    /// A value with no parts, or a value whose parts are still to read.
    fn value_head(&mut self) -> Result<Result<Value, OpenValue>, String> {
        let at = self.i;
        let t = self.tag(13, "a value")?;
        Ok(Ok(match t {
            0 => Value::Bool(self.tag(1, "a boolean")? == 1),
            1 => Value::Int(self.n()? as i64),
            2 => Value::int(self.big()?),
            3 => {
                let (num, den) = (self.big()?, BigInt::from(self.magnitude()?));
                match Rat::new(num, den) {
                    Some(r) => Value::rat(r),
                    None => return self.err(at, "a rational with denominator 0"),
                }
            }
            12..=15 => {
                let rational = t == 13 || t == 15;
                let num = self.big()?;
                let den = match rational {
                    true => BigInt::from(self.magnitude()?),
                    false => BigInt::from(1),
                };
                let count = self.len()?;
                let mut pows = Vec::with_capacity(count);
                for _ in 0..count {
                    pows.push((self.n()?, self.big()?));
                }
                let mut wide = Vec::new();
                if t >= 14 {
                    let count = self.len()?;
                    for _ in 0..count {
                        wide.push((self.magnitude()?, self.big()?));
                    }
                    // The writer gives tags 14 and 15 only to a number with a wide atom.
                    if wide.is_empty() {
                        return self.err(at, "a number with no wide atom under a wide tag");
                    }
                }
                let r = match Rat::from_kept_wide(num, den, pows, wide) {
                    Some(r) if rational || r.is_integer() => r,
                    _ => return self.err(at, "a number not in the form it is kept in"),
                };
                match rational {
                    true => Value::Rat(Arc::new(r)),
                    // A `Big` is never in the 64-bit range: an integer there is an `Int`
                    // (`Value::integer`), and the order and the keys of maps rely on it. The
                    // writer gives tag 12 only to a `Big`, so a tag-12 integer in the range is
                    // damaged data (test `a_kept_wide_integer_in_the_64_bit_range_is_refused`).
                    false => match Value::integer(r) {
                        v @ Value::Big(_) => v,
                        _ => {
                            return self
                                .err(at, "an integer in the 64-bit range written as a wide one");
                        }
                    },
                }
            }
            4 => Value::float(f64::from_bits(self.n()?)),
            11 => match u32::try_from(self.n()?) {
                Ok(bits) => Value::float32(f32::from_bits(bits)),
                Err(_) => return self.err(at, "an f32 word wider than 32 bits"),
            },
            5 => Value::Str(self.text()?),
            6 => {
                let name = self.name()?;
                let fields: Vec<String> = self.many(Self::name)?;
                let left = self.len()?;
                return Ok(Err(OpenValue::Atom {
                    at,
                    name,
                    fields,
                    args: Vec::with_capacity(left),
                    left,
                }));
            }
            10 => Value::atom_with(self.name()?, Vec::new()),
            7 | 8 => {
                let path = t == 8;
                let left = self.len()?;
                return Ok(Err(OpenValue::Items(path, Vec::with_capacity(left), left)));
            }
            _ => {
                let left = self.len()?;
                return Ok(Err(OpenValue::Family(
                    at,
                    Vec::with_capacity(left),
                    None,
                    left,
                )));
            }
        }))
    }

    /// The value `o`, all its parts read.
    fn close_value(&self, o: OpenValue) -> Result<Value, String> {
        Ok(match o {
            OpenValue::Atom {
                at,
                name,
                fields,
                args,
                ..
            } => {
                if fields.windows(2).any(|w| w[0] >= w[1]) {
                    return self.err(
                        at,
                        format!("atom `#{name}` has its fields out of order or repeated"),
                    );
                }
                if !fields.is_empty() && fields.len() != args.len() {
                    return self.err(
                        at,
                        format!(
                            "atom `#{name}` has {} fields and {} values",
                            fields.len(),
                            args.len()
                        ),
                    );
                }
                Value::Atom(Atom {
                    name: name.into(),
                    fields: fields.into_iter().map(Into::into).collect(),
                    payload: (!args.is_empty()).then(|| args.into()),
                })
            }
            OpenValue::Items(false, vs, _) => Value::tuple(vs),
            OpenValue::Items(true, vs, _) => Value::path(vs),
            OpenValue::Family(at, entries, _, _) => match text::family(entries) {
                Ok(f) => Value::Family(f),
                Err(e) => return self.err(at, e),
            },
        })
    }

    fn evidence(&mut self) -> Result<Evidence, String> {
        let items = self.many(|r| {
            let k = r.name()?;
            Ok((k.into(), GRADES[r.tag(5, "a grade")? as usize]))
        })?;
        Ok(items.into_iter().collect())
    }

    fn op(&mut self) -> Result<Op, String> {
        Ok(match self.tag(16, "an operation")? {
            0 => Op::Reindex(Witness::Residue),
            1 => Op::Reindex(Witness::Catalog(self.s()?.into())),
            2 => Op::Discard,
            3 => Op::Fold {
                depth: self.idx()?,
                identity: self.tag(1, "a boolean")? == 1,
                ev: self.evidence()?,
            },
            4 => Op::Fix {
                lattice: self.tag(1, "a boolean")? == 1,
                ev: self.evidence()?,
            },
            5 => Op::Gen(match self.tag(1, "a guard position")? {
                0 => GuardPos::Before,
                _ => GuardPos::After,
            }),
            6 => Op::Read(self.checked(text::not_a_port)?.into()),
            7 => Op::Push(self.checked(text::not_a_port)?.into()),
            8 => Op::Fam,
            9 => Op::Derived(DERIVED[self.tag(3, "a derived node")? as usize]),
            10 => Op::Prim(PRIMS[self.tag(PRIMS.len() as u8 - 1, "a primitive")? as usize]),
            11 => Op::Apply,
            12 => Op::Lambda,
            13 => Op::If,
            14 => Op::Match(self.many(Self::pattern)?),
            15 => Op::Rec,
            _ => Op::Wave,
        })
    }

    /// Reads a pattern from a stack of the patterns begun and not yet ended, in the order
    /// [`W::pattern`] writes it: patterns nest as deep as the program (step T2-mid).
    fn pattern(&mut self) -> Result<Pattern, String> {
        let mut open: Vec<OpenPattern> = Vec::new();
        loop {
            let mut got = match self.pattern_head()? {
                Ok(p) => Some(p),
                Err(o) => {
                    open.push(o);
                    None
                }
            };
            loop {
                let Some(top) = open.last_mut() else {
                    return Ok(got.expect("a pattern read"));
                };
                if let Some(p) = got.take() {
                    top.put(p);
                }
                if top.left() > 0 {
                    // A field pattern's part follows its name.
                    if let OpenPattern::Fields(_, _, key @ None, _) = top {
                        *key = Some(self.name()?.into());
                    }
                    break;
                }
                got = Some(open.pop().expect("the top").close());
            }
        }
    }

    /// A pattern with no parts, or a pattern whose parts are still to read.
    fn pattern_head(&mut self) -> Result<Result<Pattern, OpenPattern>, String> {
        let t = self.tag(7, "a pattern")?;
        Ok(Ok(match t {
            0 => Pattern::Wild,
            1 => Pattern::Bind(self.binder()?.into()),
            2 => Pattern::Lit(self.value()?),
            3 | 5 => {
                let name = match t {
                    3 => Some(self.name()?.into()),
                    _ => None,
                };
                let left = self.len()?;
                return Ok(Err(OpenPattern::Items(
                    name,
                    Vec::with_capacity(left),
                    left,
                )));
            }
            4 => {
                let name = self.name()?.into();
                let left = self.len()?;
                return Ok(Err(OpenPattern::Fields(
                    name,
                    Vec::with_capacity(left),
                    None,
                    left,
                )));
            }
            6 => Pattern::AnyAtom,
            _ => {
                let at = self.i;
                let s = self.s()?;
                Pattern::Is(
                    text::parse_type(&s)
                        .or_else(|e| self.err(at, format!("the type `{s}`: {e}")))?,
                )
            }
        }))
    }
}

/// A tuple or path (`true`), an atom, or a family whose parts are being read, with the number
/// of parts, or of entries, still to read.
enum OpenValue {
    Atom {
        at: usize,
        name: String,
        fields: Vec<String>,
        args: Vec<Value>,
        left: usize,
    },
    Items(bool, Vec<Value>, usize),
    /// The byte it starts at, the entries read, and the key of the entry being read.
    Family(usize, Vec<(Value, Value)>, Option<Value>, usize),
}

impl OpenValue {
    fn left(&self) -> usize {
        match self {
            OpenValue::Atom { left, .. } | OpenValue::Items(_, _, left) => *left,
            OpenValue::Family(_, _, _, left) => *left,
        }
    }

    fn put(&mut self, v: Value) {
        match self {
            OpenValue::Atom { args, left, .. } | OpenValue::Items(_, args, left) => {
                args.push(v);
                *left -= 1;
            }
            OpenValue::Family(_, entries, key, left) => match key.take() {
                None => *key = Some(v),
                Some(k) => {
                    entries.push((k, v));
                    *left -= 1;
                }
            },
        }
    }
}

/// An atom pattern (named) or a tuple pattern, or a fields pattern with the field of the part
/// being read, whose parts are being read, with the number still to read.
enum OpenPattern {
    Items(Option<Arc<str>>, Vec<Pattern>, usize),
    Fields(Arc<str>, Vec<(Arc<str>, Pattern)>, Option<Arc<str>>, usize),
}

impl OpenPattern {
    fn left(&self) -> usize {
        match self {
            OpenPattern::Items(_, _, left) | OpenPattern::Fields(_, _, _, left) => *left,
        }
    }

    fn put(&mut self, p: Pattern) {
        match self {
            OpenPattern::Items(_, ps, left) => {
                ps.push(p);
                *left -= 1;
            }
            OpenPattern::Fields(_, fs, key, left) => {
                fs.push((key.take().expect("the field read"), p));
                *left -= 1;
            }
        }
    }

    fn close(self) -> Pattern {
        match self {
            OpenPattern::Items(Some(name), ps, _) => Pattern::Atom(name, ps),
            OpenPattern::Items(None, ps, _) => Pattern::Tuple(ps),
            OpenPattern::Fields(name, fs, _, _) => Pattern::Fields(name, fs),
        }
    }
}
