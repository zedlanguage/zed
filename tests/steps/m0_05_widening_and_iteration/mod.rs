//! Step M0.5: widening and iteration.
//!
//! The store's iteration (DESIGN.md sec:constraints rule 1) is fixed down to the traversal:
//! the weak topological order of the dependency graph, the widening points, the two phases,
//! the landmarks at which a widening or a narrowing stops a bound, and the tonicity and
//! interval-revision tables. Each piece
//! is checked against an independent implementation written here from the definition:
//! `wto` against the declarative definition of the order, `iteration` against a flattened
//! stack machine and against the concrete least fixpoint, `widening` for the termination
//! bound of every lattice, and `revision` on constraints from ordinary programs.

mod bench;
mod complete;
mod invariant;
mod iteration;
mod order;
mod revision;
mod scaling;
mod schedule;
mod widening;
mod wto;

use std::collections::BTreeSet;

use zed_kernel::Value;
use zed_kernel::provenance::Vector;
use zed_tests::instances::Rng;
use zedc::address::ContentAddress;
use zedc::lex::Span;
use zedc::store::interval::{End, IntervalSet, Num};
use zedc::store::iterate::Equations;
use zedc::store::landmarks::Landmarks;
use zedc::store::wto::VertexKey;

/// One term of a cell's transfer: `(cell[from] ⊓ filter) + offset`.
#[derive(Clone, Debug)]
struct Term {
    from: usize,
    filter: IntervalSet,
    offset: i64,
}

/// The canonical form of a cell's equation, written with the names of the cells it reads and
/// not their numbers: its initial value, then each term's cell, filter and offset.
type Form = (String, Vec<(String, String, i64)>);

/// A system of interval equations, `cell[v] = init[v] ⊔ ⋃ terms[v]`: the shape the store's
/// equations take for loop counters, accumulators and bounds checks. Each cell has a key:
/// its binding name, the content address of its equation, the equation's canonical form and
/// the keypath of its fact address, empty unless a test gives one. Cell `v` is written at the
/// span [`line`]`(v)`.
#[derive(Clone, Debug)]
struct System {
    init: Vec<IntervalSet>,
    terms: Vec<Vec<Term>>,
    reads: Vec<Vec<usize>>,
    /// Whether the equations give no landmarks, as if the program wrote no bound.
    bare: bool,
    names: Vec<String>,
    addresses: Vec<ContentAddress>,
    forms: Vec<Form>,
    keypaths: Vec<Vector<Value>>,
    spans: Vec<Span>,
}

impl System {
    /// The system with cell `v` named `c{v}`.
    fn new(init: Vec<IntervalSet>, terms: Vec<Vec<Term>>) -> Self {
        let names = (0..init.len()).map(|v| format!("c{v}")).collect();
        System::named(names, init, terms)
    }

    /// The system with the given names, which several cells may share, as the nodes of one
    /// binding's expression do; each cell's address is the hash of its form.
    fn named(names: Vec<String>, init: Vec<IntervalSet>, terms: Vec<Vec<Term>>) -> Self {
        let n = names.len();
        let reads = terms
            .iter()
            .map(|ts| {
                let mut r: Vec<usize> = ts.iter().map(|t| t.from).collect();
                r.sort_unstable();
                r.dedup();
                r
            })
            .collect();
        let forms: Vec<Form> = init
            .iter()
            .zip(&terms)
            .map(|(i, ts)| {
                let ts = ts
                    .iter()
                    .map(|t| (names[t.from].clone(), t.filter.to_string(), t.offset));
                (i.to_string(), ts.collect())
            })
            .collect();
        let addresses = forms
            .iter()
            .map(|f| ContentAddress(*blake3::hash(format!("{f:?}").as_bytes()).as_bytes()))
            .collect();
        System {
            init,
            terms,
            reads,
            bare: false,
            names,
            addresses,
            forms,
            keypaths: vec![Vector::new(); n],
            spans: (0..n).map(line).collect(),
        }
    }

    /// The same system with its cells renumbered: cell `v` of the result is cell `old[v]`.
    fn renumbered(&self, old: &[usize]) -> System {
        let mut new = vec![0; old.len()];
        for (v, &o) in old.iter().enumerate() {
            new[o] = v;
        }
        let terms = old
            .iter()
            .map(|&o| {
                self.terms[o]
                    .iter()
                    .map(|t| Term {
                        from: new[t.from],
                        ..t.clone()
                    })
                    .collect()
            })
            .collect();
        let mut s = System::named(
            old.iter().map(|&o| self.names[o].clone()).collect(),
            old.iter().map(|&o| self.init[o].clone()).collect(),
            terms,
        );
        s.addresses = old.iter().map(|&o| self.addresses[o]).collect();
        s.forms = old.iter().map(|&o| self.forms[o].clone()).collect();
        s.keypaths = old.iter().map(|&o| self.keypaths[o].clone()).collect();
        s.spans = old.iter().map(|&o| self.spans[o]).collect();
        s.bare = self.bare;
        s
    }

    /// The same equations with no landmarks.
    fn bare(self) -> Self {
        System { bare: true, ..self }
    }

    /// A random system of up to 8 cells, each reading up to 3 cells.
    fn random(rng: &mut Rng) -> Self {
        let n = 1 + rng.below(8);
        let mut init = Vec::new();
        let mut terms = Vec::new();
        for _ in 0..n {
            init.push(match rng.below(3) {
                0 => IntervalSet::empty(),
                _ => {
                    let lo = rng.int(-5, 5);
                    IntervalSet::of(lo, lo + rng.int(0, 3))
                }
            });
            let ts = (0..rng.below(4))
                .map(|_| Term {
                    from: rng.below(n),
                    filter: random_filter(rng),
                    offset: rng.int(-2, 2),
                })
                .collect();
            terms.push(ts);
        }
        System::new(init, terms)
    }

    /// The concrete least fixpoint over sets of integers, cut to `window`: every value a
    /// cell takes in an execution that stays in the window. The cut makes it a subset of the
    /// true least fixpoint, so it is a lower bound that every sound solution contains.
    fn concrete(&self, window: (i64, i64)) -> Vec<BTreeSet<i64>> {
        let n = self.init.len();
        let mut cells = vec![BTreeSet::new(); n];
        loop {
            let mut changed = false;
            for v in 0..n {
                let mut next: BTreeSet<i64> = (window.0..=window.1)
                    .filter(|&x| self.init[v].contains(x))
                    .collect();
                for t in &self.terms[v] {
                    for &x in &cells[t.from] {
                        let y = x + t.offset;
                        if t.filter.contains(x) && (window.0..=window.1).contains(&y) {
                            next.insert(y);
                        }
                    }
                }
                if next != cells[v] {
                    cells[v] = next;
                    changed = true;
                }
            }
            if !changed {
                return cells;
            }
        }
    }
}

fn random_filter(rng: &mut Rng) -> IntervalSet {
    match rng.below(4) {
        0 => IntervalSet::top(),
        1 => IntervalSet::range(End::NegInf, End::of(rng.int(-3, 8))),
        2 => IntervalSet::range(End::of(rng.int(-8, 3)), End::PosInf),
        _ => {
            let lo = rng.int(-6, 4);
            IntervalSet::of(lo, lo + rng.int(0, 6))
        }
    }
}

impl Equations<IntervalSet> for System {
    type Form = Form;
    type Keypath = Vector<Value>;
    fn reads(&self) -> &[Vec<usize>] {
        &self.reads
    }
    fn key(&self, v: usize) -> VertexKey<'_, Form, Vector<Value>> {
        VertexKey {
            name: &self.names[v],
            address: self.addresses[v],
            form: &self.forms[v],
            keypath: &self.keypaths[v],
        }
    }
    fn span(&self, v: usize) -> Span {
        self.spans[v]
    }
    fn eval(&self, v: usize, cells: &[IntervalSet]) -> IntervalSet {
        self.terms[v].iter().fold(self.init[v].clone(), |acc, t| {
            let moved = cells[t.from]
                .meet(&t.filter)
                .lift1(|(lo, hi)| vec![(shift(lo, t.offset), shift(hi, t.offset))]);
            acc.join(&moved)
        })
    }
    /// The finite ends of cell `v`'s initial value and filters.
    fn landmarks(&self, v: usize) -> Landmarks {
        if self.bare {
            return Landmarks::none();
        }
        let sets = [&self.init[v]]
            .into_iter()
            .chain(self.terms[v].iter().map(|t| &t.filter));
        let ends = sets.flat_map(|s| s.pieces().flat_map(|(lo, hi)| [lo, hi]));
        Landmarks::of(
            ends.filter_map(|e| match e {
                End::Fin(v) => Some(v.clone()),
                _ => None,
            }),
            [],
        )
    }
}

fn shift(e: &End, by: i64) -> End {
    match e {
        End::Fin(v) => End::Fin(v + &Num::from(by)),
        e => e.clone(),
    }
}

/// Whether every cell contains its own projection: a post-fixpoint, which is what phase 1
/// must reach and phase 2 must keep.
fn is_post_fixpoint(eq: &System, cells: &[IntervalSet]) -> bool {
    (0..cells.len()).all(|v| eq.eval(v, cells).is_subset(&cells[v]))
}

/// `[lo, hi]` with `None` for an infinite end, for readable expectations.
fn iv(lo: Option<i64>, hi: Option<i64>) -> IntervalSet {
    IntervalSet::range(
        lo.map_or(End::NegInf, End::of),
        hi.map_or(End::PosInf, End::of),
    )
}

/// The key of cell `v` of a system whose cells are told apart by their names alone.
fn name_key(names: &[String], v: usize) -> VertexKey<'_, (), ()> {
    VertexKey {
        name: &names[v],
        address: ContentAddress([0; 32]),
        form: &(),
        keypath: &(),
    }
}

/// The span of cell `v` of a system written one equation to a line of ten bytes.
fn line(v: usize) -> Span {
    Span {
        start: 10 * v,
        end: 10 * v + 9,
    }
}

/// The names `n0000`, `n0001`, …: their order is the order of the numbers.
fn numbered_names(n: usize) -> Vec<String> {
    (0..n).map(|v| format!("n{v:04}")).collect()
}
