//! A value the kernel hands back is allocated with one cell per shared sequence: when a part
//! of it holds one tuple or payload in two places, that tuple is one cell counted once per
//! holder, on the native path (`Heap::fresh`) and in the counting machine (`Machine::fresh`).
//! So a song whose every verse sings the one below twice is a cell per verse, `d` cells, and
//! not one per path, `2^d` (COMPLEXITY.md R9, item HEAP-fresh-dag). Sharing is by the
//! sequence's identity, never by equal contents: two equal sequences built apart stay two cells.

use std::sync::Arc;

use zed_kernel::term::build::{app, lit, prim};
use zed_kernel::value::{Atom, Items};
use zed_kernel::{Evaluator, Lookup, Prim, Term, Value, World};
use zed_tests::scaling;
use zedc::zir::memory;

use super::planned;

/// A song of `d` verses: the bottom verse is the line `"la"`, and each verse above it sings the
/// verse below twice, `(below, below)`, the one value in both places.
fn song(d: usize) -> Value {
    (0..d).fold(Value::str("la"), |below, _| {
        Value::tuple(vec![below.clone(), below])
    })
}

/// A lookup port that gives the same value for every key, as a record store does for a key it
/// keeps one record under.
#[derive(Debug)]
struct Same(Value);

impl Lookup for Same {
    fn get(&self, _: &Value) -> Result<Value, String> {
        Ok(self.0.clone())
    }
}

/// `v` as the input `song` and as the record of port `db` for every key.
fn world(v: &Value) -> World {
    let mut w = World::new();
    w.inputs.insert("song".into(), v.clone());
    let port: Arc<dyn Lookup> = Arc::new(Same(v.clone()));
    w.sources.insert("db".into(), port);
    w
}

/// `read song`, made by the runtime from the input.
fn read() -> Term {
    Term::Read("song".into())
}

/// `db(0)`, made by the kernel, which runs the port.
fn looked_up() -> Term {
    app(Term::Read("db".into()), vec![lit(0i64)])
}

/// The value of `t` in `w` and the cells allocated, after checking that the kernel, the
/// counting machine and native code agree on the value, that the machine and native code make
/// the same allocations, increments and decrements, and that each frees every cell it made.
fn cells(t: &Term, w: &World) -> (Value, u64) {
    let k = Evaluator::new(w.clone()).run(t).unwrap();
    let (g, p) = planned(t);
    let (v, s) = memory::run(g.graph(), &p, &mut Evaluator::new(w.clone())).unwrap();
    let o = zed_native::run(&g, &p, &mut Evaluator::new(w.clone())).unwrap();
    // Both values share their sequences with the input, so these comparisons read no part twice.
    assert_eq!(v, k);
    assert_eq!(o.value, k);
    let native = (o.stats.increments, o.stats.decrements, o.stats.allocations);
    assert_eq!(native, (s.increments, s.decrements, s.allocations), "{t}");
    assert_eq!(
        s.frees, s.allocations,
        "{t}: a cell of the machine is live at the end"
    );
    assert_eq!(
        o.stats.frees, o.stats.allocations,
        "{t}: a cell is live at the end"
    );
    (k, s.allocations)
}

#[test]
fn a_song_of_sixty_verses_each_singing_the_one_below_twice_is_sixty_two_cells() {
    // A cell per path would be 2^60 cells for the verses alone.
    let w = world(&song(60));
    for t in [read(), looked_up()] {
        assert_eq!(cells(&t, &w), (song(60), 62), "{t}");
    }
}

#[test]
fn the_first_half_of_a_shared_song_is_the_verse_below() {
    let s = song(40);
    let Value::Tuple(halves) = &s else {
        unreachable!("a song of verses is a tuple")
    };
    let t = prim(Prim::TupleGet, vec![looked_up(), lit(0i64)]);
    assert_eq!(cells(&t, &world(&s)), (halves[0].clone(), 42));
}

#[test]
fn a_value_held_once_is_a_cell_per_part() {
    // An order line, `("pen", ("ink", 2))`: no part is held twice.
    let line = Value::tuple(vec![
        Value::str("pen"),
        Value::tuple(vec![Value::str("ink"), Value::Int(2)]),
    ]);
    assert_eq!(cells(&read(), &world(&line)), (line, 4));
}

#[test]
fn equal_sequences_built_apart_are_two_cells() {
    // `(("la"), ("la"))` with each `("la")` built on its own: equal, not one sequence.
    let verse = || Value::tuple(vec![Value::str("la")]);
    let v = Value::tuple(vec![verse(), verse()]);
    assert_eq!(cells(&read(), &world(&v)), (v, 5));
}

#[test]
fn empty_sequences_are_never_cells() {
    // `((), (), #none)`: the empty tuple and a bare atom are uncounted, shared or not.
    let empty = Value::tuple(Vec::new());
    let v = Value::tuple(vec![empty.clone(), empty, Value::atom("none")]);
    assert_eq!(cells(&read(), &world(&v)), (v, 1));
}

#[test]
fn a_tuple_and_atoms_over_one_sequence_are_each_their_own_cell() {
    // `(("a", "b"), #pair("a", "b"), #span("a", "b"), #pair("a", "b"))` over one sequence: the
    // tuple and the two names are three cells, and the second `#pair` is the first one's.
    let xs: Items = vec![Value::str("a"), Value::str("b")].into();
    let atom = |name: &str| {
        Value::Atom(Atom {
            name: name.into(),
            fields: Default::default(),
            payload: Some(xs.clone()),
        })
    };
    let pair = atom("pair");
    let v = Value::tuple(vec![
        Value::Tuple(xs.clone()),
        pair.clone(),
        atom("span"),
        pair,
    ]);
    // The outer tuple, the inner tuple, `#pair` and `#span`, and the two strings of each.
    assert_eq!(cells(&read(), &world(&v)), (v, 10));
}

/// The depth of the scaling tests, and 8 times it.
const D: usize = 2_000;

#[test]
fn the_machine_makes_a_shared_song_in_time_linear_in_its_verses() {
    let programs = scaling::inputs(D, |d| (world(&song(d)), planned(&looked_up())));
    scaling::check(
        "memory::run of a port giving d verses each held twice",
        D,
        |d| {
            let (w, (g, p)) = &programs[&d];
            let (_, s) = memory::run(g.graph(), p, &mut Evaluator::new(w.clone())).unwrap();
            assert_eq!(s.allocations, d as u64 + 2);
        },
    );
}

#[test]
fn native_code_makes_a_shared_song_in_time_linear_in_its_verses() {
    let programs = scaling::inputs(D, |d| (world(&song(d)), planned(&looked_up())));
    scaling::check(
        "native run of a port giving d verses each held twice",
        D,
        |d| {
            let (w, (g, p)) = &programs[&d];
            let o = zed_native::run(g, p, &mut Evaluator::new(w.clone())).unwrap();
            assert_eq!(o.stats.allocations, d as u64 + 2);
        },
    );
}
