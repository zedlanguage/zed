//! The binary form of ZIR: what a build caches and the backends read.
//!
//! It begins with the four bytes `ZIR\0` and the version as a 32-bit little-endian word; the
//! root region follows. Every count, index and integer is a 64-bit little-endian word, every
//! name a count of bytes and then its UTF-8 bytes, and every choice a one-byte tag. A value is
//! written by its structure, a number outside the 64-bit range and a rational by their
//! decimal digits, and a float by its bits, so every value comes back bit for bit. An edge is
//! written as its text form ([`super::text::edge`]): a type's representation is private to
//! the kernel, and its printed form is its exact, canonical description. A primitive is its
//! index in [`PRIMS`]. A decoding error names the byte offset at which it was found.

use std::sync::Arc;

use num_bigint::BigInt;
use zed_kernel::num::Rat;
use zed_kernel::term::{Evidence, Grade, GuardPos, Pattern, Witness};
use zed_kernel::value::{Atom, Value};

use super::text::{self, PRIMS, VERSION};
use super::{Derived, Edge, Node, Op, Region, RegionKind, Src};

const MAGIC: &[u8; 4] = b"ZIR\0";

/// The one NaN word the form writes: the quiet NaN with a zero payload. Rust does not fix the
/// bits of `f64::NAN`, so the form fixes them itself.
pub const NAN_BITS: u64 = 0x7ff8_0000_0000_0000;

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

const DERIVED: [Derived; 4] = [Derived::Group, Derived::Rank, Derived::Scan, Derived::Join];

fn index<T: PartialEq>(all: &[T], x: &T) -> u8 {
    all.iter()
        .position(|y| y == x)
        .expect("every case is listed") as u8
}

// ---------------------------------------------------------------------------------------------
// Writing

/// The binary form of the graph rooted at `root`.
pub fn encode(root: &Region) -> Vec<u8> {
    let mut w = W(MAGIC.to_vec());
    w.0.extend_from_slice(&VERSION.to_le_bytes());
    w.region(root);
    w.0
}

struct W(Vec<u8>);

impl W {
    fn tag(&mut self, t: u8) {
        self.0.push(t);
    }

    fn n(&mut self, n: u64) {
        self.0.extend_from_slice(&n.to_le_bytes());
    }

    fn s(&mut self, s: &str) {
        self.n(s.len() as u64);
        self.0.extend_from_slice(s.as_bytes());
    }

    fn many<T>(&mut self, xs: &[T], mut f: impl FnMut(&mut Self, &T)) {
        self.n(xs.len() as u64);
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
                    self.n(r.nodes.len() as u64);
                    jobs.push(Job::Results(&r.results));
                    jobs.extend(r.nodes.iter().rev().map(Job::Node));
                }
                Job::Node(n) => {
                    self.op(&n.op);
                    self.many(&n.inputs, Self::src);
                    self.many(&n.outputs, Self::edge);
                    self.n(n.regions.len() as u64);
                    jobs.extend(n.regions.iter().rev().map(|r| Job::Region(r)));
                }
                Job::Results(rs) => self.many(rs, Self::src),
            }
        }
    }

    fn edge(&mut self, e: &Edge) {
        self.s(&text::edge(e));
    }

    fn src(&mut self, s: &Src) {
        match s {
            Src::Arg(i) => {
                self.tag(0);
                self.n(*i as u64);
            }
            Src::Out(k, p) => {
                self.tag(1);
                self.n(*k as u64);
                self.n(*p as u64);
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
                self.n(*i as u64);
            }
            Value::Big(b) => {
                self.tag(2);
                self.s(&b.numer_text());
            }
            Value::Rat(r) => {
                self.tag(3);
                self.s(&r.numer_text());
                self.s(&r.denom_text());
            }
            Value::Float(x) => {
                self.tag(4);
                let x = x.get();
                self.n(if x.is_nan() { NAN_BITS } else { x.to_bits() });
            }
            Value::Str(s) => {
                self.tag(5);
                // The text is written block by block, as `s` writes one block.
                self.n(s.len() as u64);
                s.chunks()
                    .for_each(|c| self.0.extend_from_slice(c.as_bytes()));
            }
            Value::Atom(a) => {
                self.tag(6);
                self.s(&a.name);
                self.many(&a.fields, |w, f| w.s(f));
                self.n(a.args.len() as u64);
                jobs.extend(a.args.iter().rev());
            }
            Value::Tuple(vs) => {
                self.tag(7);
                self.n(vs.len() as u64);
                jobs.extend(vs.iter().rev());
            }
            Value::Path(vs) => {
                self.tag(8);
                self.n(vs.len() as u64);
                jobs.extend(vs.iter().rev());
            }
            Value::Family(f) => {
                self.tag(9);
                let entries: Vec<_> = f.iter().collect();
                self.n(entries.len() as u64);
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
            w.s(k);
            w.tag(index(&GRADES, g));
        });
    }

    fn op(&mut self, op: &Op) {
        match op {
            Op::Reindex(Witness::Residue) => self.tag(0),
            Op::Reindex(Witness::Catalog(entry)) => {
                self.tag(1);
                self.s(entry);
            }
            Op::Discard => self.tag(2),
            Op::Fold {
                depth,
                identity,
                ev,
            } => {
                self.tag(3);
                self.n(*depth as u64);
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
                self.s(port);
            }
            Op::Push(port) => {
                self.tag(7);
                self.s(port);
            }
            Op::Fam => self.tag(8),
            Op::Derived(d) => {
                self.tag(9);
                self.tag(index(&DERIVED, d));
            }
            Op::Prim(p) => {
                self.tag(10);
                self.tag(index(&PRIMS, p));
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
                self.s(k);
            }
            match p {
                Pattern::Wild => self.tag(0),
                Pattern::Bind(x) => {
                    self.tag(1);
                    self.s(x);
                }
                Pattern::Lit(v) => {
                    self.tag(2);
                    self.value(v);
                }
                Pattern::Atom(name, ps) => {
                    self.tag(3);
                    self.s(name);
                    self.n(ps.len() as u64);
                    jobs.extend(ps.iter().rev().map(|q| (None, q)));
                }
                Pattern::Fields(name, fs) => {
                    self.tag(4);
                    self.s(name);
                    self.n(fs.len() as u64);
                    jobs.extend(fs.iter().rev().map(|(k, q)| (Some(&**k), q)));
                }
                Pattern::Tuple(ps) => {
                    self.tag(5);
                    self.n(ps.len() as u64);
                    jobs.extend(ps.iter().rev().map(|q| (None, q)));
                }
                Pattern::AnyAtom => self.tag(6),
                Pattern::Is(t) => {
                    self.tag(7);
                    self.s(&t.to_string());
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Reading

/// The graph encoded in `bytes`, which [`super::validate`] has not yet checked.
pub fn decode(bytes: &[u8]) -> Result<Region, String> {
    let mut r = R { b: bytes, i: 0 };
    if r.take(4)? != MAGIC {
        return Err("byte 0: the data does not start `ZIR\\0`".into());
    }
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
    Ok(root)
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

    fn s(&mut self) -> Result<String, String> {
        let n = self.len()?;
        let at = self.i;
        match std::str::from_utf8(self.take(n)?) {
            Ok(s) => Ok(s.into()),
            Err(_) => self.err(at, "a name is not UTF-8"),
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

    fn big(&mut self) -> Result<BigInt, String> {
        let at = self.i;
        let s = self.s()?;
        s.parse()
            .or_else(|_| self.err(at, format!("`{s}` is not an integer")))
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
        let t = self.tag(9, "a value")?;
        Ok(Ok(match t {
            0 => Value::Bool(self.tag(1, "a boolean")? == 1),
            1 => Value::Int(self.n()? as i64),
            2 => Value::int(self.big()?),
            3 => {
                let (num, den) = (self.big()?, self.big()?);
                match Rat::new(num, den) {
                    Some(r) => Value::rat(r),
                    None => return self.err(at, "a rational with denominator 0"),
                }
            }
            4 => Value::float(f64::from_bits(self.n()?)),
            5 => Value::str(&self.s()?),
            6 => {
                let name = self.s()?;
                let fields: Vec<String> = self.many(Self::s)?;
                let left = self.len()?;
                return Ok(Err(OpenValue::Atom {
                    at,
                    name,
                    fields,
                    args: Vec::with_capacity(left),
                    left,
                }));
            }
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
                    args: args.into(),
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
            let k = r.s()?;
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
            6 => Op::Read(self.s()?.into()),
            7 => Op::Push(self.s()?.into()),
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
                        *key = Some(self.s()?.into());
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
            1 => Pattern::Bind(self.s()?.into()),
            2 => Pattern::Lit(self.value()?),
            3 | 5 => {
                let name = match t {
                    3 => Some(self.s()?.into()),
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
                let name = self.s()?.into();
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
