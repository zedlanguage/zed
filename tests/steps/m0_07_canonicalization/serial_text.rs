//! Rows SPEC-m07-string-serial, SPEC-m07-tag-table and SPEC-m07-prim-codes: the address step
//! M0.7 defines, computed here by a serializer of its own that writes each node as M0.7's
//! tables say, against the implementation's address and bytes.
//!
//! M0.7: "The serialization gives every node a tag byte and its fields in order, lengths and
//! integers as 64-bit little-endian words and strings as their length then UTF-8, [...] any
//! other free variable by its name. A kernel term's address is BLAKE3-256 over `zed-canon` and
//! a NUL byte, the 32-bit little-endian rule-set version, then the serialization." The tables
//! after that step give every node's tag, its fields in order and the kind each is written as,
//! and every primitive's code; `sync` copies them to `zed/fences/canon-serial.md`, which
//! [`m07`] reads. The tag, the order of the fields, how each is written and the code of a
//! primitive all come from the tables, so a change to
//! crates/zedc-zir/src/canon/serial.rs that the tables do not make, or the reverse, fails
//! [`the_serialization_is_m07s_byte_for_byte`], and a changed code fails
//! [`every_primitive_has_the_code_m07_gives`]. Only which row a node or a primitive is (a
//! lambda is the row Lambda, `Prim::Add` the row `a + b`) and the parts of each node are
//! written here.
//!
//! The terms compared hold no nonempty string, so the two must agree. Terms holding nonempty
//! strings (short, long, repeated, all distinct, joined) are compared in the parked test
//! /home/luke/Work/wt/failing-tests/SPEC-m07-string-serial.rs: since canonicalization
//! VERSION 11 (CANON-term-string-nodes) the implementation writes a nonempty string as the
//! rules of its canonical parse, not as its UTF-8, and the two differ (QUESTIONS A106).

use std::collections::BTreeSet;

use num_bigint::BigInt;
use zed_kernel::term::Prim;
use zed_kernel::term::build::{lam, var};
use zed_kernel::value::Value;
use zedc::address::ContentAddress;
use zedc::canon::{Def, Domain};
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::lattice::{Congruence, FiniteSet, Lattice};

use super::{def, facet, none};

/// Step M0.7's serialization and address, by its tables.
pub(super) mod m07 {
    use std::collections::{BTreeMap, BTreeSet};
    use std::sync::LazyLock;

    use num_bigint::{BigInt, Sign};
    use zed_kernel::term::{Evidence, FixKind, Grade, GuardPos, Pattern, Prim, Term, Witness};
    use zed_kernel::value::Value;
    use zedc::address::ContentAddress;
    use zedc::canon::binders::level_of;
    use zedc::canon::{Def, Domain};
    use zedc::store::interval::End;
    use zedc::store::lattice::Congruence;

    /// The copy `sync` makes of M0.7's tables.
    pub const COPY: &str = include_str!("../../../zed/fences/canon-serial.md");

    /// What a free variable naming another definition resolves to.
    pub type Refs<'a> = &'a dyn Fn(&str) -> Option<ContentAddress>;

    /// A row of a table: its tag, none for a part, and its fields, each a name and a kind.
    #[derive(Clone, Debug)]
    pub struct Row {
        pub tag: Option<u8>,
        pub fields: Vec<(String, String)>,
    }

    /// The tables, by the kind of node each lists, lowercase, and in each its rows by name,
    /// lowercase.
    pub type Tables = BTreeMap<String, BTreeMap<String, Row>>;

    /// The end of the header of each table with tags.
    const TAGS: &str = " | Tag | Fields in order |";

    /// The header of the table of the primitives' codes.
    pub const CODES: &str = "| Primitive | Code |";

    /// The tables of `text`, laid out as `sync` copies them: a header `| Kind | Tag | Fields
    /// in order |` starts each table, and each row is `| Name | tag or — | `fields` or — |`,
    /// the fields `name: kind` separated by `, `. The table of codes ([`codes_of`]) is left
    /// out.
    pub fn parse(text: &str) -> Tables {
        let mut tables = Tables::new();
        let mut current = None;
        let mut in_codes = false;
        for line in text.lines() {
            if line == CODES {
                in_codes = true;
            }
            if in_codes && !line.ends_with(TAGS) {
                continue;
            }
            in_codes = false;
            let cells: Vec<&str> = line
                .strip_prefix("| ")
                .and_then(|l| l.strip_suffix(" |"))
                .unwrap_or_else(|| panic!("not a row of a table: {line}"))
                .split(" | ")
                .collect();
            let [name, tag, fields] = cells[..] else {
                panic!("a row of three cells: {line}")
            };
            if tag == "Tag" {
                let kind = name.to_lowercase();
                assert!(!tables.contains_key(&kind), "two tables of {kind}");
                tables.insert(kind.clone(), BTreeMap::new());
                current = Some(kind);
                continue;
            }
            let table = current.as_ref().expect("a row after a header");
            let tag = match tag {
                "—" => None,
                t => Some(t.parse().unwrap_or_else(|_| panic!("a tag byte: {line}"))),
            };
            let fields = match fields {
                "—" => vec![],
                f => f
                    .trim_matches('`')
                    .split(", ")
                    .map(|f| {
                        let (n, k) = f.split_once(": ").expect("a field `name: kind`");
                        (n.to_string(), k.to_string())
                    })
                    .collect(),
            };
            let rows = tables.get_mut(table).expect("its table");
            let old = rows.insert(name.to_lowercase(), Row { tag, fields });
            assert!(old.is_none(), "two rows {name} in {table}");
        }
        tables
    }

    /// The tables of the copy.
    pub fn tables() -> &'static Tables {
        static TABLES: LazyLock<Tables> = LazyLock::new(|| parse(COPY));
        &TABLES
    }

    /// The table of the primitives' codes in `text`, laid out as `sync` copies it: the header
    /// [`CODES`], then rows `| primitive | code |` up to the next table's header; each
    /// primitive by its cell, with `\|` read as `|`.
    pub fn codes_of(text: &str) -> BTreeMap<String, u64> {
        let mut codes = BTreeMap::new();
        let mut inside = false;
        for line in text.lines() {
            if line == CODES {
                assert!(!inside && codes.is_empty(), "two tables of codes");
                inside = true;
                continue;
            }
            if !inside || line.ends_with(TAGS) {
                inside = false;
                continue;
            }
            let (primitive, code) = line
                .strip_prefix("| ")
                .and_then(|l| l.strip_suffix(" |"))
                .and_then(|l| l.rsplit_once(" | "))
                .unwrap_or_else(|| panic!("a row of two cells: {line}"));
            let code = code.parse().unwrap_or_else(|_| panic!("a code: {line}"));
            let old = codes.insert(primitive.replace("\\|", "|"), code);
            assert!(old.is_none(), "two rows {primitive}");
        }
        codes
    }

    /// The codes of the copy.
    pub fn codes() -> &'static BTreeMap<String, u64> {
        static CODES: LazyLock<BTreeMap<String, u64>> = LazyLock::new(|| codes_of(COPY));
        &CODES
    }

    /// Which row of the table of codes the primitive `p` is.
    pub fn row_of(p: Prim) -> &'static str {
        use Prim::*;
        match p {
            Add => "`a + b`",
            Sub => "`a - b`",
            Mul => "`a * b`",
            Div => "`a / b`",
            IntDiv => "`a div b`",
            Mod => "`a mod b`",
            Neg => "`-a`",
            Eq => "`a == b`",
            Ne => "`a != b`",
            Lt => "`a < b`",
            Le => "`a <= b`",
            Gt => "`a > b`",
            Ge => "`a >= b`",
            And => "`a && b`",
            Or => "`a || b`",
            Not => "`!a`",
            Min => "`min`",
            Max => "`max`",
            Get => "`f[k]` on a family",
            Count => "`f.count`",
            Union => "`f.union(g)`",
            Path => "a key path built from its keys",
            PathKey => "the key at a given position of a key path",
            PathLen => "the number of keys of a key path",
            Tuple => "a tuple `(a, b, …)`",
            TupleGet => "`t[i]` on a tuple",
            Concat => "`a ++ b` on two strings",
            Pow => "`a ^ b`",
            Atom => "an atom built from its name, its field names and its payload",
            Show => "`String`",
            CastInt => "`int`",
            CastRat => "`rat`",
            CastF64 => "`f64`",
            Abs => "`abs`",
            Len => "`len`",
            Lower => "`lower`",
            Upper => "`upper`",
            Trim => "`trim`",
            Sum => "`sum`",
            BitAnd => "`bitAnd`",
            BitOr => "`bitOr`",
            BitXor => "`bitXor`",
            BitNot => "`bitNot`",
            Shl => "`shl`",
            Shr => "`shr`",
            PopCount => "`popCount`",
            LeadingZeros => "`leadingZeros`",
            TrailingZeros => "`trailingZeros`",
            Rotl => "`rotl`",
            Rotr => "`rotr`",
            F64Bits => "`f64Bits`",
            CodePoint => "`codePoint`",
            Scalar => "`scalar`",
            Utf8 => "`utf8`",
            FromUtf8 => "`fromUtf8`",
            MulHi => "`mulHi`",
            BitReverse => "`bitReverse`",
            ByteSwap => "`byteSwap`",
            Pdep => "`pdep`",
            Pext => "`pext`",
            FunnelShl => "`funnelShl`",
            FunnelShr => "`funnelShr`",
            At => "`f[k]` on a family whose keys are one integer interval, each present",
            CastF32 => "`f32`",
            Sqrt => "`sqrt`",
            Fma => "`fma`",
            Entries => "a family display `{k0 -> v0, k1 -> v1, …}`",
            Has => "`k in f`",
            Range => "`range`",
            FirstEntry => "the first entry of a level in key order",
            LastEntry => "the last entry of a level in key order",
            EntryAfter => "the entry after a given one of a level in key order",
            EntryBefore => "the entry before a given one of a level in key order",
            First => "`f.first`",
            Last => "`f.last`",
            Split => "`split`",
            Lines => "`lines`",
            Join => "`concat`",
            RangeFrom => "`a ..`, the integers from `a` with no upper end",
            ListConcat => "`a ++ b` on two lists",
            Place => "a function value with the parameter list of the function it holds",
            CallNamed => "a call through a function value, placed by the function called",
        }
    }

    /// The code of `p` in the copy.
    pub fn code(p: Prim) -> u64 {
        let row = row_of(p);
        *codes()
            .get(row)
            .unwrap_or_else(|| panic!("M0.7's table of codes has no row {row}"))
    }

    /// A node or a field as the serializer has it: which row a node is and its parts by the
    /// names the tables give them, before the tables say in which order and how they are
    /// written.
    #[derive(Debug)]
    pub enum Piece {
        Byte(u8),
        Word(u64),
        Str(String),
        Utf8(Vec<u8>),
        Address([u8; 32]),
        List(Vec<Piece>),
        Opt(Option<Box<Piece>>),
        /// A row of a table with tags, by its name.
        Node(&'static str, Vec<(&'static str, Piece)>),
        /// A row of the table of parts, which has no tag.
        Part(Vec<(&'static str, Piece)>),
    }

    use Piece::*;

    /// Writes pieces as `tables` says, and records each row it writes.
    pub struct Writer<'t> {
        pub tables: &'t Tables,
        pub out: Vec<u8>,
        pub used: BTreeSet<(String, String)>,
    }

    impl Writer<'_> {
        fn word(&mut self, n: u64) {
            self.out.extend_from_slice(&n.to_le_bytes());
        }

        /// Writes `piece` as a field of kind `kind`.
        pub fn write(&mut self, kind: &str, piece: Piece) {
            match (kind, piece) {
                ("byte", Byte(b)) => self.out.push(b),
                ("word", Word(n)) => self.word(n),
                ("string", Str(s)) => {
                    self.word(s.len() as u64);
                    self.out.extend_from_slice(s.as_bytes());
                }
                ("utf8", Utf8(b)) => self.out.extend_from_slice(&b),
                ("address", Address(a)) => self.out.extend_from_slice(&a),
                (k, List(items)) if k.starts_with("list of ") => {
                    self.word(items.len() as u64);
                    items.into_iter().for_each(|i| self.write(&k[8..], i));
                }
                (k, Opt(x)) if k.starts_with("option of ") => match x {
                    None => self.out.push(0),
                    Some(x) => {
                        self.out.push(1);
                        self.write(&k[10..], *x);
                    }
                },
                (k, Node(row, parts)) if k != "part" && self.tables.contains_key(k) => {
                    self.row(k, row, parts)
                }
                (k, Part(parts)) => self.row("part", k, parts),
                (k, piece) => panic!("the tables write {k} where the serializer has {piece:?}"),
            }
        }

        /// Writes the row `name` of the table `table`: its tag, then each field the row lists,
        /// in its order, taken by name from `parts`, which must hold those fields and no other.
        fn row(&mut self, table: &str, name: &str, mut parts: Vec<(&'static str, Piece)>) {
            let row = self.tables[table]
                .get(name)
                .unwrap_or_else(|| panic!("the table {table} has no row {name}"))
                .clone();
            self.used.insert((table.to_string(), name.to_string()));
            if let Some(t) = row.tag {
                self.out.push(t);
            }
            for (field, kind) in &row.fields {
                let i = parts
                    .iter()
                    .position(|(f, _)| f == field)
                    .unwrap_or_else(|| panic!("{table} {name}: the serializer has no {field}"));
                let (_, piece) = parts.remove(i);
                self.write(kind, piece);
            }
            let rest: Vec<_> = parts.iter().map(|(f, _)| *f).collect();
            assert!(
                rest.is_empty(),
                "{table} {name}: the table lists no field {rest:?}"
            );
        }
    }

    /// The address of `d`, already in normal form, under rule-set version `version`:
    /// BLAKE3-256 over `zed-canon`, a NUL byte, the version as a 32-bit little-endian word,
    /// then the serialization.
    pub fn address(version: u32, d: &Def) -> ContentAddress {
        let mut h = blake3::Hasher::new();
        h.update(b"zed-canon\0");
        h.update(&version.to_le_bytes());
        h.update(&serialize(d));
        // `hashed` changes nothing outside the `short-addresses` test build, which keeps one
        // byte of every address.
        ContentAddress::hashed(&h)
    }

    /// The serialization of `d`, no free variable naming a definition.
    pub fn serialize(d: &Def) -> Vec<u8> {
        let mut w = Writer {
            tables: tables(),
            out: Vec::new(),
            used: BTreeSet::new(),
        };
        w.write("definition", definition(d, &|_| None));
        w.out
    }

    /// The definition `d` as pieces.
    pub fn definition(d: &Def, refs: Refs<'_>) -> Piece {
        let facets = d.facets.iter().map(|f| {
            Part(vec![
                ("hint", Byte(u8::from(f.hint))),
                ("kind", Str(f.kind.to_string())),
                ("value", value(&f.value)),
            ])
        });
        Part(vec![
            ("name", Str(d.name.to_string())),
            (
                "domain",
                Opt(d.domain.as_ref().map(|d| Box::new(domain(d)))),
            ),
            ("facets", List(facets.collect())),
            ("body", term(&d.body, refs)),
        ])
    }

    fn integer(n: &BigInt) -> Piece {
        Part(vec![
            ("sign", Byte(u8::from(n.sign() == Sign::Minus))),
            ("magnitude", magnitude(n)),
        ])
    }

    fn magnitude(n: &BigInt) -> Piece {
        Part(vec![(
            "limbs",
            List(n.magnitude().iter_u64_digits().map(Word).collect()),
        )])
    }

    fn end(e: &End) -> Piece {
        match e {
            End::NegInf => Node("below every integer", vec![]),
            End::PosInf => Node("above every integer", vec![]),
            End::Fin(v) => match v.to_i64() {
                Some(v) => Node("integer in i64", vec![("value", Word(v as u64))]),
                None => Node(
                    "integer past i64",
                    vec![("value", integer(&v.built().expect("memory")))],
                ),
            },
        }
    }

    fn domain(d: &Domain) -> Piece {
        let pieces = d
            .ints
            .pieces()
            .map(|(lo, hi)| Part(vec![("low", end(lo)), ("high", end(hi))]));
        let class = match &d.class {
            Congruence::Bottom => Node("no integer", vec![]),
            Congruence::Class { modulus, residue } => match (modulus.to_i64(), residue.to_i64()) {
                (Some(m), Some(r)) => Node(
                    "class in i64",
                    vec![("modulus", Word(m as u64)), ("residue", Word(r as u64))],
                ),
                _ => Node(
                    "class past i64",
                    vec![
                        ("modulus", integer(&modulus.built().expect("memory"))),
                        ("residue", integer(&residue.built().expect("memory"))),
                    ],
                ),
            },
        };
        Part(vec![("pieces", List(pieces.collect())), ("class", class)])
    }

    fn values(vs: &[Value]) -> Piece {
        List(vs.iter().map(value).collect())
    }

    pub fn value(v: &Value) -> Piece {
        match v {
            Value::Bool(b) => Node("boolean", vec![("value", Byte(u8::from(*b)))]),
            Value::Int(n) => Node("integer", vec![("value", Word(*n as u64))]),
            Value::Float(x) => Node("f64", vec![("bits", Word(x.get().to_bits()))]),
            Value::Float32(x) => Node("f32", vec![("bits", Word(u64::from(x.get().to_bits())))]),
            Value::Str(s) => {
                let mut utf8 = Vec::new();
                s.chunks()
                    .for_each(|c| utf8.extend_from_slice(c.as_bytes()));
                Node(
                    "string",
                    vec![("length", Word(s.len() as u64)), ("text", Utf8(utf8))],
                )
            }
            Value::Atom(a) => {
                let name = ("name", Str(a.name.to_string()));
                if !a.is_bare() && a.args().is_empty() {
                    Node("atom with empty payload", vec![name])
                } else if a.fields.is_empty() {
                    Node("atom", vec![name, ("payload", values(a.args()))])
                } else {
                    let fields = a.fields.iter().map(|f| Str(f.to_string())).collect();
                    Node(
                        "atom with fields",
                        vec![
                            name,
                            ("fields", List(fields)),
                            ("payload", values(a.args())),
                        ],
                    )
                }
            }
            Value::Big(r) | Value::Rat(r) => {
                let rational = matches!(v, Value::Rat(_));
                let (num, den, pows) = r.kept();
                let mut parts = vec![
                    ("sign", Byte(u8::from(num.sign() == Sign::Minus))),
                    ("numerator", magnitude(num)),
                ];
                if rational {
                    parts.push(("denominator", magnitude(den)));
                }
                if pows.is_empty() {
                    if rational {
                        return Node("rational", parts);
                    }
                    return Node("integer past i64", vec![("value", integer(num))]);
                }
                let pows = pows
                    .iter()
                    .map(|(p, e)| Part(vec![("prime", Word(*p)), ("exponent", integer(e))]));
                parts.push(("powers", List(pows.collect())));
                let row = match rational {
                    true => "rational with powers",
                    false => "integer with powers",
                };
                Node(row, parts)
            }
            Value::Tuple(vs) => Node("tuple", vec![("items", values(vs))]),
            Value::Path(vs) => Node("path", vec![("items", values(vs))]),
            Value::Family(f) => {
                let entries = f
                    .iter()
                    .map(|(k, v)| Part(vec![("key", value(k)), ("value", value(v))]));
                Node("family", vec![("entries", List(entries.collect()))])
            }
        }
    }

    fn pattern(p: &Pattern) -> Piece {
        let patterns = |ps: &[Pattern]| List(ps.iter().map(pattern).collect());
        match p {
            Pattern::Wild => Node("wildcard", vec![]),
            Pattern::Bind(_) => Node("binder", vec![]),
            Pattern::Lit(v) => Node("literal", vec![("value", value(v))]),
            Pattern::Atom(name, ps) => Node(
                "atom",
                vec![("name", Str(name.to_string())), ("payload", patterns(ps))],
            ),
            Pattern::Tuple(ps) => Node("tuple", vec![("items", patterns(ps))]),
            Pattern::AnyAtom => Node("any atom", vec![]),
            Pattern::Fields(name, fs) => {
                let fs = fs.iter().map(|(f, p)| {
                    Part(vec![("field", Str(f.to_string())), ("pattern", pattern(p))])
                });
                Node(
                    "atom with fields",
                    vec![
                        ("name", Str(name.to_string())),
                        ("fields", List(fs.collect())),
                    ],
                )
            }
            Pattern::Is(t) => Node("type test", vec![("type", Str(t.to_string()))]),
        }
    }

    fn evidence(ev: &Evidence) -> Piece {
        let grade = |g: &Grade| match g {
            Grade::Axiom => "axiom",
            Grade::CheckedExhaustive => "checked exhaustive",
            Grade::Proved => "proved",
            Grade::Bounded => "bounded",
            Grade::Obligated => "obligated",
            Grade::Assumed => "assumed",
        };
        let properties = ev.iter().map(|(p, g)| {
            Part(vec![
                ("name", Str(p.to_string())),
                ("grade", Node(grade(g), vec![])),
            ])
        });
        Part(vec![("properties", List(properties.collect()))])
    }

    pub fn term(t: &Term, refs: Refs<'_>) -> Piece {
        let term = |t: &Term| term(t, refs);
        let terms = |ts: &[Term]| List(ts.iter().map(term).collect());
        match t {
            Term::Lit(v) => Node("literal", vec![("value", value(v))]),
            Term::Var(x) => match (level_of(x), refs(x)) {
                (Some(level), _) => Node("bound variable", vec![("level", Word(level as u64))]),
                (None, Some(a)) => Node("definition", vec![("address", Address(a.0))]),
                (None, None) => Node("free variable", vec![("name", Str(x.to_string()))]),
            },
            Term::Lam(params, body) => Node(
                "lambda",
                vec![
                    ("parameters", Word(params.len() as u64)),
                    ("body", term(body)),
                ],
            ),
            Term::App(f, args) => Node(
                "application",
                vec![("function", term(f)), ("arguments", terms(args))],
            ),
            Term::Prim(p, args) => Node(
                "primitive",
                vec![("code", Word(code(*p))), ("arguments", terms(args))],
            ),
            Term::PrimFn(p) => Node("primitive as a function", vec![("code", Word(code(*p)))]),
            Term::Let(_, e, body) => Node("let", vec![("value", term(e)), ("body", term(body))]),
            Term::If(c, a, b) => Node(
                "if",
                vec![("condition", term(c)), ("then", term(a)), ("else", term(b))],
            ),
            Term::Match(e, arms) => {
                let arms = arms
                    .iter()
                    .map(|(p, a)| Part(vec![("pattern", pattern(p)), ("body", term(a))]));
                Node(
                    "match",
                    vec![("scrutinee", term(e)), ("arms", List(arms.collect()))],
                )
            }
            Term::Fam { domain, body, .. } => {
                Node("fam", vec![("domain", term(domain)), ("body", term(body))])
            }
            Term::Reindex {
                family,
                kf,
                vf,
                witness,
            } => {
                let witness = match witness {
                    Witness::Residue => Node("residue", vec![]),
                    Witness::Catalog(n) => Node("catalog", vec![("name", Str(n.to_string()))]),
                };
                Node(
                    "reindex",
                    vec![
                        ("family", term(family)),
                        ("kf", term(kf)),
                        ("vf", term(vf)),
                        ("witness", witness),
                    ],
                )
            }
            Term::Discard { family, sel } => Node(
                "discard",
                vec![("family", term(family)), ("sel", term(sel))],
            ),
            Term::Fold {
                family,
                op,
                identity,
                depth,
                ev,
            } => Node(
                "fold",
                vec![
                    ("family", term(family)),
                    ("op", term(op)),
                    (
                        "identity",
                        Opt(identity.as_ref().map(|i| Box::new(term(i)))),
                    ),
                    ("depth", Word(*depth as u64)),
                    ("ev", evidence(ev)),
                ],
            ),
            Term::Fix {
                init,
                step,
                kind,
                ev,
                ..
            } => {
                let kind = match kind {
                    FixKind::Lattice { join } => Node("lattice", vec![("join", term(join))]),
                    FixKind::Definedness => Node("definedness", vec![]),
                };
                Node(
                    "fix",
                    vec![
                        ("init", term(init)),
                        ("step", term(step)),
                        ("kind", kind),
                        ("ev", evidence(ev)),
                    ],
                )
            }
            Term::Gen {
                init,
                step,
                guard,
                pos,
            } => {
                let pos = match pos {
                    GuardPos::Before => Node("before", vec![]),
                    GuardPos::After => Node("after", vec![]),
                };
                Node(
                    "gen",
                    vec![
                        ("init", term(init)),
                        ("step", term(step)),
                        ("guard", term(guard)),
                        ("position", pos),
                    ],
                )
            }
            Term::Read(port) => Node("port read", vec![("port", Str(port.to_string()))]),
            Term::Push(port, v) => Node(
                "port push",
                vec![("port", Str(port.to_string())), ("value", term(v))],
            ),
        }
    }
}

fn implementation(d: &zedc::canon::Def) -> ContentAddress {
    zedc::canon::address(d, &none).expect("memory for the address")
}

/// Definitions from a shipping-cost table with no nonempty string: integers, booleans, a
/// tuple, a free variable (the prelude's `max`), primitives, and the empty string.
fn without_text() -> Vec<zedc::canon::Def> {
    use zed_kernel::term::build::{app, lit, prim, var};
    vec![
        def("free_over", lit(Value::Int(5000))),
        def("negative", lit(Value::Int(-17))),
        def("express", lit(Value::Bool(true))),
        def(
            "rates",
            lit(Value::tuple(vec![
                Value::Int(499),
                Value::Int(899),
                Value::tuple(vec![Value::Bool(false), Value::Int(0)]),
            ])),
        ),
        def(
            "cost",
            app(
                var("max"),
                vec![
                    prim(Prim::Add, vec![lit(Value::Int(499)), lit(Value::Int(150))]),
                    lit(Value::Int(0)),
                ],
            ),
        ),
        def("no_note", lit(Value::str(""))),
        def(
            "notes",
            lit(Value::tuple(vec![Value::str(""), Value::Int(3)])),
        ),
    ]
}

/// `index: <domain> = i` as a definition.
fn index(ints: IntervalSet, class: Congruence) -> Def {
    Def {
        name: "index".into(),
        domain: Some(Domain {
            ints,
            class,
            finite: FiniteSet::Top,
        }),
        facets: vec![facet("unit", Value::str(""))],
        body: var("i"),
    }
}

/// One definition of every node of M0.7's tables, but a nonempty string: the definitions
/// without text; one per term, value and pattern of the completeness cases (cases.rs), each
/// under a lambda; domains with ends and classes in and past `i64`, and one admitting
/// nothing; and a variable naming another definition (`other`), with what resolves it.
fn every_node() -> Vec<Def> {
    let past = BigInt::from(1) << 70;
    let mut defs = without_text();
    defs.extend(
        super::cases::catalog("x")
            .into_iter()
            .filter(|t| !matches!(t, zed_kernel::Term::Lit(Value::Str(s)) if !s.is_empty()))
            .map(|t| def("k", lam(&["x"], t))),
    );
    defs.extend([
        index(IntervalSet::of(0, 10), Congruence::new(4, 1)),
        index(IntervalSet::top(), Congruence::top()),
        index(IntervalSet::of(2, 4), Congruence::new(4, 1)),
        index(
            IntervalSet::range(End::Fin(Num::from(&past)), End::PosInf),
            Congruence::new(Num::from(&past + 1), 3),
        ),
        index(
            IntervalSet::range(End::NegInf, End::Fin(Num::from(-&past))),
            Congruence::top(),
        ),
        def("uses", var("other")),
    ]);
    defs
}

/// What resolves `other`, the one definition the cases name.
fn refs(x: &str) -> Option<ContentAddress> {
    (x == "other").then_some(ContentAddress([7; 32]))
}

/// The serialization of `d` by M0.7's tables `tables`, and the rows it wrote.
fn by_tables(d: &Def, tables: &m07::Tables) -> (Vec<u8>, BTreeSet<(String, String)>) {
    let mut w = m07::Writer {
        tables,
        out: Vec::new(),
        used: BTreeSet::new(),
    };
    w.write("definition", m07::definition(d, &refs));
    (w.out, w.used)
}

/// Where M0.7 states the serialization, the implementation's address is M0.7's: the header,
/// the rule-set version, words, names and the empty string.
#[test]
fn a_definition_without_text_has_the_address_m07_states() {
    for d in without_text() {
        assert_eq!(
            implementation(&d),
            m07::address(zedc::canon::VERSION, &d),
            "{}",
            d.name
        );
    }
}

/// The comparison can fail: the address under another rule-set version, or with one byte of
/// the serialization changed, is not the implementation's.
#[test]
fn another_version_or_byte_gives_another_address() {
    for d in without_text() {
        let ours = implementation(&d);
        assert_ne!(
            ours,
            m07::address(zedc::canon::VERSION - 1, &d),
            "{}",
            d.name
        );
        let mut bytes = m07::serialize(&d);
        let last = bytes.len() - 1;
        bytes[last] ^= 1;
        let mut h = blake3::Hasher::new();
        h.update(b"zed-canon\0");
        h.update(&zedc::canon::VERSION.to_le_bytes());
        h.update(&bytes);
        if !zed_kernel::address::SHORT {
            assert_ne!(ours, ContentAddress::hashed(&h), "{}", d.name);
        }
    }
}

/// The implementation's serialization is the one M0.7's tables give, byte for byte, on a
/// definition of every node they list but a nonempty string; and every row of every table is
/// written by some definition, so a row the implementation no longer writes fails too.
#[test]
fn the_serialization_is_m07s_byte_for_byte() {
    let tables = m07::tables();
    let mut used = BTreeSet::new();
    for d in every_node() {
        let normal = zedc::canon::canonicalize(&d);
        let (bytes, rows) = by_tables(&normal, tables);
        assert_eq!(
            zedc::canon::serialize(&normal, &refs).expect("memory"),
            bytes,
            "{}: {}",
            d.name,
            normal.body
        );
        used.extend(rows);
    }
    let all: BTreeSet<(String, String)> = tables
        .iter()
        .flat_map(|(t, rows)| rows.keys().map(|r| (t.clone(), r.clone())))
        .collect();
    let unused: Vec<_> = all.difference(&used).collect();
    assert!(unused.is_empty(), "rows no definition writes: {unused:?}");
}

/// Each primitive's code is the one M0.7's table gives it (row SPEC-m07-prim-codes), so a code
/// changed in `Prim::code` or in the table fails here; the table has one row for each
/// primitive, and no code twice.
#[test]
fn every_primitive_has_the_code_m07_gives() {
    let prims = zedc::zir::text::PRIMS;
    for p in prims {
        assert_eq!(
            p.code(),
            m07::code(p),
            "{p:?}, the row {} of M0.7's table",
            m07::row_of(p)
        );
    }
    let rows: BTreeSet<&str> = prims.iter().map(|p| m07::row_of(*p)).collect();
    let table: BTreeSet<&str> = m07::codes().keys().map(String::as_str).collect();
    assert_eq!(rows, table, "the table's rows are the primitives'");
    assert_eq!(table.len(), prims.len(), "one row for each primitive");
    let codes: BTreeSet<u64> = m07::codes().values().copied().collect();
    assert_eq!(codes.len(), prims.len(), "no code twice");
}

/// The serializer reads the tables: with the tag of Lambda changed, or two fields of
/// Application swapped, in the copy, its bytes are no longer the implementation's.
#[test]
fn a_changed_table_gives_other_bytes() {
    let d = zedc::canon::canonicalize(&def("k", lam(&["x"], var("x"))));
    let ours = zedc::canon::serialize(&d, &refs).expect("memory");
    let apply = zedc::canon::canonicalize(&def(
        "k",
        zed_kernel::term::build::app(var("f"), vec![var("y")]),
    ));
    let theirs = zedc::canon::serialize(&apply, &refs).expect("memory");
    for (from, to, d, want) in [
        ("| Lambda | 5 |", "| Lambda | 20 |", &d, &ours),
        (
            "`function: term, arguments: list of term`",
            "`arguments: list of term, function: term`",
            &apply,
            &theirs,
        ),
    ] {
        assert_eq!(&by_tables(d, m07::tables()).0, want, "{from}");
        assert!(m07::COPY.contains(from), "{from}");
        let changed = m07::parse(&m07::COPY.replace(from, to));
        assert_ne!(&by_tables(d, &changed).0, want, "{to}");
    }
}
