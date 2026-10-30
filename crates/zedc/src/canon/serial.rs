//! The canonical serialization. Every node is a tag byte followed by its fields; a sequence
//! is its length then its items, a string its length in bytes then its UTF-8, and lengths
//! and integers are little-endian 64-bit words. Each tag fixes the fields that follow, so the
//! encoding is self-delimiting and two different normal forms never share an encoding.
//!
//! Binders are canonical by then, so a binder is written by its count alone (a lambda's
//! parameters, a pattern's `Bind`), and a bound variable by its level.

use zed_kernel::term::{Evidence, FixKind, Grade, GuardPos, Pattern, Term, Witness};
use zed_kernel::value::Value;

use super::binders::level_of;
use super::{Def, Domain};
use crate::address::ContentAddress;
use crate::store::interval::End;
use crate::store::lattice::Congruence;

type Refs<'a> = &'a dyn Fn(&str) -> Option<ContentAddress>;

struct Out<'a> {
    bytes: Vec<u8>,
    refs: Refs<'a>,
}

impl Out<'_> {
    fn tag(&mut self, t: u8) {
        self.bytes.push(t);
    }

    fn word(&mut self, n: u64) {
        self.bytes.extend_from_slice(&n.to_le_bytes());
    }

    fn str(&mut self, s: &str) {
        self.word(s.len() as u64);
        self.bytes.extend_from_slice(s.as_bytes());
    }

    fn end(&mut self, e: End) {
        match e {
            End::NegInf => self.tag(0),
            End::Fin(v) => {
                self.tag(1);
                self.word(v as u64);
            }
            End::PosInf => self.tag(2),
        }
    }

    fn domain(&mut self, d: &Domain) {
        self.word(d.ints.pieces().len() as u64);
        for &(lo, hi) in d.ints.pieces() {
            self.end(lo);
            self.end(hi);
        }
        match d.class {
            Congruence::Bottom => self.tag(0),
            Congruence::Class { modulus, residue } => {
                self.tag(1);
                self.word(modulus);
                self.word(residue as u64);
            }
        }
    }

    fn value(&mut self, v: &Value) {
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
                self.str(s);
            }
            Value::Atom(a) if a.fields.is_empty() => {
                self.tag(4);
                self.str(&a.name);
                self.values(&a.args);
            }
            Value::Atom(a) => {
                self.tag(10);
                self.str(&a.name);
                self.word(a.fields.len() as u64);
                a.fields.iter().for_each(|f| self.str(f));
                self.values(&a.args);
            }
            Value::Big(n) => {
                self.tag(8);
                self.str(&n.to_string());
            }
            Value::Rat(r) => {
                self.tag(9);
                self.str(&r.numer().to_string());
                self.str(&r.denom().to_string());
            }
            Value::Tuple(vs) => {
                self.tag(5);
                self.values(vs);
            }
            Value::Path(vs) => {
                self.tag(6);
                self.values(vs);
            }
            Value::Family(f) => {
                self.tag(7);
                self.word(f.len() as u64);
                for (k, v) in f.iter() {
                    self.value(k);
                    self.value(v);
                }
            }
        }
    }

    fn values(&mut self, vs: &[Value]) {
        self.word(vs.len() as u64);
        vs.iter().for_each(|v| self.value(v));
    }

    fn pattern(&mut self, p: &Pattern) {
        match p {
            Pattern::Wild => self.tag(0),
            Pattern::Bind(_) => self.tag(1),
            Pattern::Lit(v) => {
                self.tag(2);
                self.value(v);
            }
            Pattern::Atom(name, ps) => {
                self.tag(3);
                self.str(name);
                self.patterns(ps);
            }
            Pattern::Tuple(ps) => {
                self.tag(4);
                self.patterns(ps);
            }
            Pattern::AnyAtom => self.tag(5),
            Pattern::Fields(name, fs) => {
                self.tag(6);
                self.str(name);
                self.word(fs.len() as u64);
                for (f, p) in fs {
                    self.str(f);
                    self.pattern(p);
                }
            }
        }
    }

    fn patterns(&mut self, ps: &[Pattern]) {
        self.word(ps.len() as u64);
        ps.iter().for_each(|p| self.pattern(p));
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

    fn terms(&mut self, ts: &[Term]) {
        self.word(ts.len() as u64);
        ts.iter().for_each(|t| self.term(t));
    }

    fn term(&mut self, t: &Term) {
        match t {
            Term::Lit(v) => {
                self.tag(1);
                self.value(v);
            }
            Term::Var(x) => match level_of(x) {
                Some(level) => {
                    self.tag(2);
                    self.word(level as u64);
                }
                None => match (self.refs)(x) {
                    Some(a) => {
                        self.tag(3);
                        self.bytes.extend_from_slice(&a.0);
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
                self.term(body);
            }
            Term::App(f, args) => {
                self.tag(6);
                self.term(f);
                self.terms(args);
            }
            Term::Prim(p, args) => {
                self.tag(7);
                self.str(&format!("{p:?}"));
                self.terms(args);
            }
            Term::PrimFn(p) => {
                self.tag(8);
                self.str(&format!("{p:?}"));
            }
            Term::Let(_, e, body) => {
                self.tag(9);
                self.term(e);
                self.term(body);
            }
            Term::If(c, a, b) => {
                self.tag(10);
                self.term(c);
                self.term(a);
                self.term(b);
            }
            Term::Match(e, arms) => {
                self.tag(11);
                self.term(e);
                self.word(arms.len() as u64);
                for (p, arm) in arms {
                    self.pattern(p);
                    self.term(arm);
                }
            }
            Term::Fam { domain, body, .. } => {
                self.tag(12);
                self.term(domain);
                self.term(body);
            }
            Term::Reindex {
                family,
                kf,
                vf,
                witness,
            } => {
                self.tag(13);
                self.term(family);
                self.term(kf);
                self.term(vf);
                match witness {
                    Witness::Residue => self.tag(0),
                    Witness::Catalog(name) => {
                        self.tag(1);
                        self.str(name);
                    }
                }
            }
            Term::Discard { family, sel } => {
                self.tag(14);
                self.term(family);
                self.term(sel);
            }
            Term::Fold {
                family,
                op,
                identity,
                depth,
                ev,
            } => {
                self.tag(15);
                self.term(family);
                self.term(op);
                match identity {
                    None => self.tag(0),
                    Some(i) => {
                        self.tag(1);
                        self.term(i);
                    }
                }
                self.word(*depth as u64);
                self.evidence(ev);
            }
            Term::Fix {
                init,
                step,
                kind,
                ev,
                ..
            } => {
                self.tag(16);
                self.term(init);
                self.term(step);
                match kind {
                    FixKind::Lattice { join } => {
                        self.tag(0);
                        self.term(join);
                    }
                    FixKind::Definedness => self.tag(1),
                }
                self.evidence(ev);
            }
            Term::Gen {
                init,
                step,
                guard,
                pos,
            } => {
                self.tag(17);
                self.term(init);
                self.term(step);
                self.term(guard);
                self.tag(match pos {
                    GuardPos::Before => 0,
                    GuardPos::After => 1,
                });
            }
            Term::Read(port) => {
                self.tag(18);
                self.str(port);
            }
            Term::Push(port, v) => {
                self.tag(19);
                self.str(port);
                self.term(v);
            }
        }
    }
}

/// The serialization of a definition in normal form.
pub fn def(d: &Def, refs: Refs<'_>) -> Vec<u8> {
    let mut out = Out {
        bytes: Vec::new(),
        refs,
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
    out.bytes
}
