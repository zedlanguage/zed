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

use num_bigint::BigInt;
use zed_kernel::family::Family;
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

    fn region(&mut self, r: &Region) {
        self.tag(index(&KINDS, &r.kind));
        self.many(&r.args, Self::edge);
        self.many(&r.nodes, Self::node);
        self.many(&r.results, Self::src);
    }

    fn node(&mut self, n: &Node) {
        self.op(&n.op);
        self.many(&n.inputs, Self::src);
        self.many(&n.outputs, Self::edge);
        self.many(&n.regions, Self::region);
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

    fn value(&mut self, v: &Value) {
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
                self.s(&b.to_string());
            }
            Value::Rat(r) => {
                self.tag(3);
                self.s(&r.numer().to_string());
                self.s(&r.denom().to_string());
            }
            Value::Float(x) => {
                self.tag(4);
                let x = x.get();
                self.n(if x.is_nan() { NAN_BITS } else { x.to_bits() });
            }
            Value::Str(s) => {
                self.tag(5);
                self.s(s);
            }
            Value::Atom(a) => {
                self.tag(6);
                self.s(&a.name);
                self.many(&a.fields, |w, f| w.s(f));
                self.many(&a.args, Self::value);
            }
            Value::Tuple(vs) => {
                self.tag(7);
                self.many(vs, Self::value);
            }
            Value::Path(vs) => {
                self.tag(8);
                self.many(vs, Self::value);
            }
            Value::Family(f) => {
                self.tag(9);
                let entries: Vec<_> = f.iter().collect();
                self.many(&entries, |w, (k, v)| {
                    w.value(k);
                    w.value(v);
                });
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

    fn pattern(&mut self, p: &Pattern) {
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
                self.many(ps, Self::pattern);
            }
            Pattern::Fields(name, fs) => {
                self.tag(4);
                self.s(name);
                self.many(fs, |w, (k, p)| {
                    w.s(k);
                    w.pattern(p);
                });
            }
            Pattern::Tuple(ps) => {
                self.tag(5);
                self.many(ps, Self::pattern);
            }
            Pattern::AnyAtom => self.tag(6),
            Pattern::Is(t) => {
                self.tag(7);
                self.s(&t.to_string());
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

    fn region(&mut self) -> Result<Region, String> {
        let kind = KINDS[self.tag(4, "a region kind")? as usize];
        Ok(Region {
            kind,
            args: self.many(Self::edge)?,
            nodes: self.many(Self::node)?,
            results: self.many(Self::src)?,
        })
    }

    fn node(&mut self) -> Result<Node, String> {
        Ok(Node {
            op: self.op()?,
            inputs: self.many(Self::src)?,
            outputs: self.many(Self::edge)?,
            regions: self.many(Self::region)?,
        })
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

    fn value(&mut self) -> Result<Value, String> {
        let at = self.i;
        Ok(match self.tag(9, "a value")? {
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
                let args = self.many(Self::value)?;
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
                    args,
                })
            }
            7 => Value::Tuple(self.many(Self::value)?),
            8 => Value::Path(self.many(Self::value)?),
            _ => {
                let entries = self.many(|r| Ok((r.value()?, r.value()?)))?;
                Value::Family(Family::of(entries))
            }
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

    fn pattern(&mut self) -> Result<Pattern, String> {
        Ok(match self.tag(7, "a pattern")? {
            0 => Pattern::Wild,
            1 => Pattern::Bind(self.s()?.into()),
            2 => Pattern::Lit(self.value()?),
            3 => Pattern::Atom(self.s()?.into(), self.many(Self::pattern)?),
            4 => Pattern::Fields(
                self.s()?.into(),
                self.many(|r| Ok((r.s()?.into(), r.pattern()?)))?,
            ),
            5 => Pattern::Tuple(self.many(Self::pattern)?),
            6 => Pattern::AnyAtom,
            _ => {
                let at = self.i;
                let s = self.s()?;
                Pattern::Is(
                    text::parse_type(&s)
                        .or_else(|e| self.err(at, format!("the type `{s}`: {e}")))?,
                )
            }
        })
    }
}
