//! The canonical serialization. Every node is a tag byte followed by its fields; a sequence
//! is its length then its items, a name or other written word its length in bytes then its
//! UTF-8, and lengths and integers are little-endian 64-bit words. An exact number past `i64`
//! is its sign as a tag, then the limbs of its numerator, and of a rational its denominator, in
//! lowest terms; one kept with prime powers, such as `2^2^100`, is the form it is kept in, its
//! numerator, denominator and powers, with no digits built
//! ([`Rat::kept`](zed_kernel::num::Rat::kept)).
//! A string value is its length in bytes, then its bytes in its type's encoding, UTF-8 for
//! `Utf8String` (DESIGN.md M0.7; author answer A106, 2026-11-20), whatever tree of blocks
//! holds it ([`Out::string`]).
//! Each tag fixes the fields that follow, so the encoding is self-delimiting and two different
//! normal forms never share an encoding.
//!
//! Binders are canonical by then, so a binder is written by its count alone (a lambda's
//! parameters, a pattern's `Bind`), and a bound variable by its level.
//!
//! # Every string an address writes is a literal (row PROOF-address-reads-literals-only)
//!
//! Writing a string costs its bytes, so a string built by `++` from a short literal, `s ++ s`
//! doubled k times, would cost 2^k. No address writes one. The claim: every string this
//! serializer writes for the program address (step L1.19b, `zedc::run::Program::address`)
//! or for an import pin (step L2.8, `zedc::query::Db::address`, `zedc::pin::address`) is a
//! piece of text the source writes (a literal or a name, the prelude's included) or one of
//! the target names of `zedc::build::TARGETS`, never a string computed from others. Proof,
//! by the path a term takes to [`def`]:
//!
//! 1. Both addresses take the term elaboration made, and nothing evaluated. The program
//!    address takes `Program::term` of the unit `zedc::front` elaborated, or, for a staged
//!    program, the term of the unit before staging (`Program::address` reads
//!    `self.unstaged`); a pin takes `front::compile` of the unit's text, which lexes, parses,
//!    resolves, replaces each read of `build` by its literal (`zedc::build::read`),
//!    elaborates and checks linearity, and runs no term (`front.rs` `staged`). Neither calls
//!    staging (step L1.28), the evaluator or the native code.
//! 2. Elaboration (`zedc-elab`) builds a string value at these sites only, each read from
//!    the syntax tree: a string literal's text parts (`elab::walk::string`, one `Term::Lit`
//!    per part, the holes and the joins left as terms: `Prim::Concat` and `String(hole)`
//!    applications); the empty string (`string` with no part, `fp_ops::strings_term`'s
//!    `concat` separator); a port's, parameter's, field's or atom's name (`state.rs`
//!    `name` and `push`, `walk.rs` named arguments and atom fields); a string literal pattern
//!    (`Pattern::Lit`). `zedc::build::read` puts `build.target` in as a string literal, one of
//!    `TARGETS`, before elaboration. Elaboration calls no evaluator and folds no primitive
//!    (no `zed_kernel::eval` or `words` call in `zedc-elab`), so `a ++ b` stays
//!    `Prim::Concat` over its operands' terms, whatever they are.
//! 3. `zedc_base::interp::prelude` wraps the term in `let`s of primitives, no strings.
//! 4. The canonicalizer's rules (`canon/mod.rs`) rename binders, drop hint facets, sort
//!    facets and normalize integer facts; none makes a string (a binder's written name goes
//!    into a hint facet, which rule 2 drops before this writer runs).
//!
//! So each string value written is a copy of a token's text, a name, or a target name, and
//! writing it costs at most that text's length; addressing costs the canonicalizer's
//! O(t log t) for a term of t nodes plus, at each `Term::Lit` or pattern, the length of the
//! source text it was read from. A literal the elaborated term holds at several nodes
//! (named once, used at each) is written at each, as every other term node is. Tests
//! `l01_32_canonical_zir::string_nodes::a_program_holding_a_doubled_string_is_addressed_by_its_text`
//! and
//! `l01_32_canonical_zir::bench::string_nodes::a_doubling_program_is_addressed_in_time_linear_in_its_text`.

use crate::zir::binary::ByteOut;
use num_bigint::Sign;
use zed_kernel::num::TooLarge;
use zed_kernel::term::{Evidence, FixKind, Grade, GuardPos, Pattern, Term, Witness};
use zed_kernel::text::Text;
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

/// The bytes of a word, a string, a magnitude and an exact number, plain or kept with prime
/// powers, are the binary form's ([`ByteOut`], shared since DRY-misc-A5); the tags here are
/// this serialization's own.
impl ByteOut for Out<'_> {
    fn sink(&mut self) -> (&mut Vec<u8>, &mut Option<TooLarge>) {
        (&mut self.bytes, &mut self.refused)
    }
}

impl Out<'_> {
    /// The string `t`: tag 3, its length in bytes as a word, then its bytes in its type's
    /// encoding (UTF-8; DESIGN.md M0.7, author answer A106, 2026-11-20), read block by block
    /// from left to right ([`Text::chunks`]). Equal strings give equal bytes whatever their
    /// trees, since the bytes written are the string's bytes in order; different strings give
    /// different bytes, since the length fixes where the bytes end and the bytes read back to
    /// the string. No hash is read and nothing is assumed.
    ///
    /// Cost, O(L) for a string of L bytes, so O(n + m) for `a ++ b` with `a` of n bytes and
    /// `b` of m, whatever the shape of the tree. Proof: the walk of [`Text::chunks`] opens
    /// each tree node it meets once and returns each block once, so its steps are the nodes
    /// and blocks of the tree counted with their repeats, a node shared k times counted k
    /// times. Every block is nonempty (`zed_kernel::text::tree::Tree::Block`), so at most L
    /// blocks are met. Every `Node` has two or three nonempty parts and every `Deep` at least
    /// one part in front and one in back, so the tree, unshared, has fewer branching nodes
    /// than blocks, plus at most one empty middle for each `Deep`, itself a branching node:
    /// fewer than 2L nodes met in all. Copying the blocks puts L bytes. So the walk and the
    /// copy are O(L), and BLAKE3 over the serialization is O(L) more.
    // Complexity tradeoff: the rules of a canonical parse of the text (`Names::canonical`,
    // rows CANON-term-string-nodes and PERF-canon-flat-strings, removed), O(m log L) for m
    // nodes plus O(r) for its r rules, cost a doubled string of 2^k bytes O(k^2) where this
    // costs 2^k; but a flat literal cost 262 to 368 times a copy and a hash of its bytes, and
    // its BLAKE3-128 rule labels made equal strings serialize alike only under collision
    // resistance. The author chose the bytes (A106, 2026-11-20): every string the program
    // address and an import pin write is a literal of the source (module comment, row
    // PROOF-address-reads-literals-only), so its bytes are paid by the source text already. A
    // cached hash per tree node would not lower the cost: BLAKE3 hashes each 1 KiB chunk
    // with its position in the input (BLAKE3 specification, O'Connor, Aumasson, Neves and
    // Wilcox-O'Hearn 2020, sec. 2.1, the chunk counter `t`), and a block's position in the
    // serialization depends on everything before it, so a node's hash at one place is not its
    // hash at another; a Merkle hash over the tree would depend on the tree's shape unless
    // the tree is canonical, which is what the parse above did. Tests
    // `l01_32_canonical_zir::string_nodes`, `m0_07_canonicalization::serial_text` (the bytes
    // M0.7 states) and `l01_32_canonical_zir::bench::string_nodes` (linear in L for a flat,
    // a joined and a doubled string; at most 50 times a copy and hash of 1 MiB).
    fn string(&mut self, t: &Text) {
        self.tag(3);
        self.word(t.len() as u64);
        t.chunks().for_each(|c| self.put(c.as_bytes()));
    }

    /// An integer of an interval end or a class past `i64`: its sign as a tag, then its
    /// magnitude, as [`ByteOut::number`] writes a numerator. A kept value is written out only after
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
            Value::Float32(x) => {
                self.tag(12);
                self.word(u64::from(x.get().to_bits()));
            }
            Value::Str(s) => self.string(s),
            // `#e()`, apart from the bare `#e` (tag 4, no parts): a tag of its own keeps every
            // address of a program without it.
            Value::Atom(a) if !a.is_bare() && a.args().is_empty() => {
                self.tag(11);
                self.str(&a.name);
            }
            Value::Atom(a) if a.fields.is_empty() => {
                self.tag(4);
                self.str(&a.name);
                self.seq(a.args(), Job::Value, todo);
            }
            Value::Atom(a) => {
                self.tag(10);
                self.str(&a.name);
                self.word(a.fields.len() as u64);
                a.fields.iter().for_each(|f| self.str(f));
                self.seq(a.args(), Job::Value, todo);
            }
            // A number with a wide atom (plan row KEPT-power-form): its kept form and its atoms
            // (`ByteOut::wide`), never built; tags 15 and 16 are new, so no other value's
            // bytes changed.
            Value::Big(n) if !n.wide().is_empty() => {
                self.tag(15);
                self.kept(n, false);
                self.wide(n);
            }
            Value::Rat(r) if !r.wide().is_empty() => {
                self.tag(16);
                self.kept(r, true);
                self.wide(r);
            }
            Value::Big(n) if n.kept().2.is_empty() => {
                self.tag(8);
                self.number(n, false);
            }
            Value::Rat(r) if r.kept().2.is_empty() => {
                self.tag(9);
                self.number(r, true);
            }
            Value::Big(n) => {
                self.tag(13);
                self.kept(n, false);
            }
            Value::Rat(r) => {
                self.tag(14);
                self.kept(r, true);
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
/// the memory to build or write one of its exact numbers
/// ([`Rat::built_parts`](zed_kernel::num::Rat::built_parts), [`Num::built`]) or to grow the
/// bytes.
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

#[cfg(test)]
mod tests {
    use zed_kernel::term::build::lit;

    use super::*;

    fn holding(strings: &[Text]) -> Def {
        Def {
            name: "s".into(),
            domain: None,
            facets: Vec::new(),
            body: lit(Value::Tuple(
                strings.iter().cloned().map(Value::Str).collect(),
            )),
        }
    }

    /// The bytes M0.7 states for the string `s`: tag 3, its length in bytes as a 64-bit
    /// little-endian word, its UTF-8 bytes.
    fn as_bytes(s: &[u8]) -> Vec<u8> {
        let mut one = vec![3u8];
        one.extend_from_slice(&(s.len() as u64).to_le_bytes());
        one.extend_from_slice(s);
        one
    }

    /// A string is written as tag 3, its length and its bytes, the same for every tree that
    /// holds it: one block, two joined blocks, and a doubled string sharing its halves.
    #[test]
    fn a_string_is_its_length_then_its_bytes_whatever_its_tree() {
        let none = |_: &str| None;
        let s = "héllo, wörld";
        let flat = Text::from(s);
        let joined = Text::join(&Text::from(&s[..3]), &Text::from(&s[3..])).unwrap();
        let half = Text::from("ab");
        let doubled = Text::join(&half, &half).unwrap();
        let a = def(&holding(&[flat.clone(), doubled.clone()]), &none).unwrap();
        let b = def(&holding(&[joined, Text::from("abab")]), &none).unwrap();
        assert_eq!(a, b);
        let mut want = as_bytes(s.as_bytes());
        want.extend(as_bytes(b"abab"));
        assert!(a.windows(want.len()).any(|w| w == &want[..]));
        // One byte changed, one length changed: different bytes.
        let c = def(
            &holding(&[Text::from("héllo, wörle"), doubled.clone()]),
            &none,
        )
        .unwrap();
        let d = def(&holding(&[flat, Text::from("aba")]), &none).unwrap();
        assert_ne!(a, c);
        assert_ne!(a, d);
        // The empty string is its tag and a zero length.
        let e = def(&holding(&[Text::from("")]), &none).unwrap();
        assert!(e.windows(9).any(|w| w == &as_bytes(b"")[..]));
    }

    /// The bytes of a definition whose body is the number `v`, in hexadecimal.
    fn number_hex(v: Value) -> String {
        let d = Def {
            name: "n".into(),
            domain: None,
            facets: Vec::new(),
            body: lit(v),
        };
        let bytes = def(&d, &|_: &str| None).unwrap();
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Plan row KEPT-power-form: wide atoms (step L1.17b) change the content address of a
    /// number that holds one and of no other. Each number below without a wide atom has the
    /// bytes origin/main 39bdc7f17 wrote for it, printed by this test there; each with one,
    /// `(2^64 + 13)^3` as an `int` and its reciprocal as a `rat`, was built in full there and
    /// is now written with tag 15 or 16, its kept form and its atoms.
    #[test]
    fn only_a_number_with_a_wide_atom_changed_its_bytes() {
        use num_bigint::{BigInt, BigUint};
        use zed_kernel::Rat;
        let int = |n: BigInt| Value::int(n);
        let recip = |r: &Rat| Rat::int(BigInt::from(1)).div(r).unwrap().unwrap();
        let two: BigInt = BigInt::from(2);
        let b: BigInt = (BigInt::from(1) << 64u32) + 13;
        let kept = Rat::int(two.clone()).pow(&BigUint::from(100u32)).unwrap();
        let third = Rat::new(BigInt::from(1), BigInt::from(3)).unwrap();
        // The bytes origin/main 80c93acf5 wrote, printed by this test there (2026-11-23).
        let unchanged = [
            (
                "small int",
                int(BigInt::from(-5)),
                "01000000000000006e0000000000000000000101fbffffffffffffff",
            ),
            (
                "plain wide int",
                int(b.clone()),
                "01000000000000006e00000000000000000001080002000000000000000d00000000000000010000\
                 0000000000",
            ),
            (
                "kept prime power",
                Value::integer(kept.clone()),
                "01000000000000006e000000000000000000010d000100000000000000010000000000000001000000\
                 00000000020000000000000000010000000000000064000000000000\
                 00",
            ),
            (
                "plain rat",
                Value::rat(third.clone()),
                "01000000000000006e00000000000000000001090001000000000000000100000000000000010000\
                 00000000000300000000000000",
            ),
            (
                "rat with a kept power",
                Value::rat(recip(&kept).mul(&third).unwrap()),
                "01000000000000006e000000000000000000010e000100000000000000010000000000000001000000\
                 0000000003000000000000000100000000000000020000000000000001010000000000000064000000\
                 00000000",
            ),
        ];
        for (what, v, before) in unchanged {
            assert_eq!(number_hex(v), before, "{what}");
        }
        // The bytes before the body's value: those of `0`, less its tag 1 and its word.
        let zero = number_hex(Value::Int(0));
        let head = &zero[..zero.len() - 18];
        let cube = Rat::int(b.clone()).pow(&BigUint::from(3u32)).unwrap();
        for (what, v, tag) in [
            ("wide int", Value::integer(cube.clone()), "0f"),
            ("wide rat", Value::rat(recip(&cube)), "10"),
        ] {
            let hex = number_hex(v);
            println!("{what}: {hex}");
            assert!(hex.starts_with(&format!("{head}{tag}")), "{what}: {hex}");
        }
    }
}
