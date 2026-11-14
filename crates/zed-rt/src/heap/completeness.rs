//! Completeness tests of the heap (row TEST-complete-crates, author P189): each way a word, a
//! cell and a pattern meet, with expected results from the value semantics of DESIGN.md
//! (sec:kernel, sec:memory) and the counting rules of step L1.34. The case list is
//! `crates/zed-rt/COMPLETENESS.md`.

use super::*;
use zed_kernel::Family;

/// The nodes of one path, and the node at its end.
fn one_path(p: &[usize]) -> (Paths, usize) {
    let mut paths = Paths::default();
    let end = p.iter().fold(Paths::ROOT, |at, &i| paths.push(at, i));
    (paths, end)
}

/// The rational `n / d`.
fn rat(n: i64, d: i64) -> Value {
    let int = |k: i64| Value::Int(k).as_integer().expect("an integer").into_owned();
    Value::rat(int(n).div(&int(d)).expect("in memory").expect("d is not 0"))
}

/// An integer past 64 bits.
fn big() -> Value {
    Value::int_text("123456789012345678901234567890", 10)
        .expect("in memory")
        .expect("digits")
}

/// `#err(code: 3, msg: "x")`, a struct payload.
fn err_struct() -> Value {
    Value::atom_named(
        "err",
        vec![
            ("msg".into(), Value::str("x")),
            ("code".into(), Value::Int(3)),
        ],
    )
    .expect("no repeated field")
}

/// Whether `p` matches `w`, with the binders it gives and the paths it entered.
fn matched(h: &mut Heap, p: &Pattern, w: Word) -> (bool, Vec<(Word, Vec<usize>)>, usize) {
    let mut paths = Paths::default();
    let mut out = Vec::new();
    let ok = h.matches(p, w, &mut paths, &mut out).expect("a data word");
    let binders = out.iter().map(|&(w, n)| (w, paths.path(n))).collect();
    (ok, binders, paths.below().len())
}

fn bind(x: &str) -> Pattern {
    Pattern::Bind(x.into())
}

#[test]
fn each_scalar_is_its_own_word_and_every_other_value_is_none() {
    assert_eq!(
        Word::int(-7),
        Word {
            tag: Word::INT,
            bits: -7
        }
    );
    assert_eq!(
        Word::state(),
        Word {
            tag: Word::STATE,
            bits: 0
        }
    );
    assert_eq!(
        Word::err(),
        Word {
            tag: Word::ERR,
            bits: 0
        }
    );
    let cases = [
        (Value::Int(i64::MIN), Some(Word::int(i64::MIN))),
        (Value::Int(i64::MAX), Some(Word::int(i64::MAX))),
        (
            Value::Bool(false),
            Some(Word {
                tag: Word::BOOL,
                bits: 0,
            }),
        ),
        (
            Value::Bool(true),
            Some(Word {
                tag: Word::BOOL,
                bits: 1,
            }),
        ),
        (
            Value::float(-0.0),
            Some(Word {
                tag: Word::FLOAT,
                bits: (-0.0f64).to_bits() as i64,
            }),
        ),
        (Value::str("a"), None),
        (Value::tuple(vec![]), None),
        (Value::atom("e"), None),
        (Value::float32(1.5), None),
        (big(), None),
        (rat(1, 3), None),
    ];
    for (v, w) in cases {
        assert_eq!(Word::scalar(&v), w, "{v:?}");
    }
    // Every NaN is the one canonical NaN (sec:kernel): two NaNs of other bits give one word.
    let other_nan = f64::from_bits(0x7ff8_0000_0000_0001);
    assert!(other_nan.is_nan());
    assert_eq!(
        Word::scalar(&Value::float(other_nan)),
        Word::scalar(&Value::float(f64::NAN))
    );
    // 0.0 and -0.0 are different values, so different words.
    assert_ne!(
        Word::scalar(&Value::float(0.0)),
        Word::scalar(&Value::float(-0.0))
    );
}

#[test]
fn a_cell_word_holds_its_index_and_generation_at_their_ends() {
    for (i, g) in [
        (0, 0),
        (1, 0),
        (0, 1),
        (INDEX_MASK as usize, 0),
        (0, GENERATIONS - 1),
        (INDEX_MASK as usize, GENERATIONS - 1),
        (12345, 678),
    ] {
        let w = Word::cell(i, g);
        assert_eq!(
            (w.tag, w.index(), w.generation()),
            (Word::CELL, i, g),
            "({i}, {g})"
        );
    }
}

#[test]
fn a_pair_is_held_in_place_and_any_other_length_apart() {
    let ws: Vec<Word> = (0..4).map(Word::int).collect();
    for n in 0..4 {
        let from_slice = Parts::from(&ws[..n]);
        let from_vec = Parts::from(ws[..n].to_vec());
        assert_eq!(&*from_slice, &ws[..n], "{n} parts from a slice");
        assert_eq!(&*from_vec, &ws[..n], "{n} parts from a vector");
        assert_eq!(
            matches!(from_slice, Parts::Two(_)),
            n == 2,
            "{n} from a slice"
        );
        assert_eq!(
            matches!(from_vec, Parts::Two(_)),
            n == 2,
            "{n} from a vector"
        );
    }
}

#[test]
fn the_parts_of_each_kind_of_cell() {
    let ws = [Word::int(1), Word::int(2), Word::int(3)];
    let objs = [
        (Obj::Str("s".into()), 0),
        (Obj::Tuple(ws[..1].into()), 1),
        (Obj::Tuple(ws[..2].into()), 2),
        (
            Obj::Atom {
                name: "a".into(),
                fields: Fields::default(),
                args: ws.into(),
            },
            3,
        ),
        (Obj::Data(Box::new(big())), 0),
        (
            Obj::Clo {
                lambda: 0,
                caps: ws[..2].into(),
            },
            2,
        ),
        (
            Obj::Clo {
                lambda: 1,
                caps: Box::new([]),
            },
            0,
        ),
    ];
    for (o, n) in objs {
        assert_eq!(o.parts(), &ws[..n], "{o:?}");
    }
}

#[test]
fn the_table_enters_each_empty_tuple_and_bare_atom_once_and_other_constants_each_time() {
    let mut h = Heap::new();
    // Scalars are words, no entry.
    for v in [Value::Int(3), Value::Bool(true), Value::float(2.5)] {
        assert_eq!(Some(h.uncounted(v.clone())), Word::scalar(&v));
    }
    assert_eq!(h.table_len(), 0);
    let unit = h.uncounted(Value::tuple(vec![]));
    let e = h.uncounted(Value::atom("e"));
    let e_empty = h.uncounted(Value::atom_with("e", vec![]));
    let f = h.uncounted(Value::atom("f"));
    assert_eq!(h.table_len(), 4);
    assert_eq!(h.uncounted(Value::tuple(vec![])), unit);
    assert_eq!(h.uncounted(Value::atom("e")), e);
    assert_eq!(h.uncounted(Value::atom_with("e", vec![])), e_empty);
    assert_eq!(h.uncounted(Value::atom("f")), f);
    assert_eq!(h.table_len(), 4, "made again, the entry it had");
    // A constant with parts is entered at each call: the compiled code enters each once.
    let k = Value::tuple(vec![Value::Int(1)]);
    let a = h.uncounted(k.clone());
    let b = h.uncounted(k.clone());
    assert_ne!(a, b);
    assert_eq!(h.table_len(), 6);
    for (w, v) in [
        (unit, Value::tuple(vec![])),
        (e, Value::atom("e")),
        (e_empty, Value::atom_with("e", vec![])),
        (a, k.clone()),
        (b, k),
    ] {
        assert_eq!(w.tag, Word::VAL);
        assert_eq!(h.value_ref(w), &v);
        assert_eq!(h.value(w).unwrap(), v);
    }
    let s = h.uncounted(Value::str("constant"));
    assert_eq!(h.value(s).unwrap(), Value::str("constant"));
    assert_eq!(h.stats.allocations, 0, "no constant is a cell");
}

#[test]
fn a_freed_cell_is_taken_again_last_freed_first_in_its_next_generation() {
    let mut h = Heap::new();
    let ws: Vec<Word> = (0..3)
        .map(|i| h.alloc(Obj::Str(i.to_string().as_str().into())))
        .collect();
    assert_eq!((h.live(), h.cell_slots(), h.stats.peak), (3, 3, 3));
    h.dec(ws[0]).unwrap();
    h.dec(ws[2]).unwrap();
    assert_eq!((h.live(), h.cell_slots(), h.stats.frees), (1, 3, 2));
    let a = h.alloc(Obj::Str("a".into()));
    let b = h.alloc(Obj::Str("b".into()));
    assert_eq!((a.index(), a.generation()), (2, 1));
    assert_eq!((b.index(), b.generation()), (0, 1));
    let c = h.alloc(Obj::Str("c".into()));
    assert_eq!(
        (c.index(), c.generation()),
        (3, 0),
        "a new cell when none is free"
    );
    assert_eq!(
        (h.live(), h.cell_slots(), h.stats.peak, h.stats.allocations),
        (4, 4, 4, 6)
    );
    // The old words of the cells taken again are freed words.
    assert!(h.value(ws[0]).is_err() && h.value(ws[2]).is_err());
    assert_eq!(h.value(b).unwrap(), Value::str("b"));
}

#[test]
fn a_fresh_value_takes_a_cell_for_each_boxed_part_and_none_for_a_scalar_or_constant() {
    let pair = Value::tuple(vec![Value::Int(1), Value::str("s")]);
    let cases: Vec<(Value, u64)> = vec![
        (Value::Int(5), 0),
        (Value::Bool(true), 0),
        (Value::float(1.0), 0),
        (Value::tuple(vec![]), 0),
        (Value::atom("e"), 0),
        (Value::atom_with("e", vec![]), 0),
        (Value::str(""), 1),
        (Value::str("é"), 1),
        (big(), 1),
        (rat(-2, 3), 1),
        (Value::float32(0.5), 1),
        (Value::path(vec![Value::Int(1), Value::str("k")]), 1),
        (Value::Family(Family::new()), 1),
        (Value::tuple(vec![Value::Int(1)]), 1),
        (pair.clone(), 2),
        (
            Value::tuple(vec![pair.clone(), Value::tuple(vec![]), Value::atom("e")]),
            3,
        ),
        (Value::atom_with("some", vec![Value::Int(3)]), 1),
        (
            Value::atom_with("some", vec![Value::str("x"), Value::Int(3)]),
            2,
        ),
        (err_struct(), 2),
        (
            Value::atom_with("n", vec![Value::atom_with("n", vec![Value::str("deep")])]),
            3,
        ),
    ];
    for (v, cells) in cases {
        let mut h = Heap::new();
        let w = h.fresh(&v).unwrap();
        assert_eq!(h.stats.allocations, cells, "cells of {v:?}");
        assert_eq!(h.live(), cells, "live cells of {v:?}");
        assert_eq!(h.value(w).unwrap(), v, "value of {v:?}");
        h.dec(w).unwrap();
        assert_eq!(h.live(), 0, "dropping {v:?} frees each of its cells");
        assert_eq!(h.stats.frees, cells, "frees of {v:?}");
    }
}

#[test]
fn a_shared_sequence_is_one_cell_counted_once_per_holder() {
    let inner = Value::tuple(vec![Value::str("a"), Value::str("b")]);
    // `inner` is held twice in `outer` and once here: shared.
    let outer = Value::tuple(vec![inner.clone(), inner.clone()]);
    let mut h = Heap::new();
    let w = h.fresh(&outer).unwrap();
    // The outer tuple, one inner tuple and its two strings.
    assert_eq!(
        (h.stats.allocations, h.stats.increments, h.stats.shared),
        (4, 1, 1)
    );
    assert_eq!(h.value(w).unwrap(), outer);
    h.dec(w).unwrap();
    assert_eq!(h.live(), 0);
    // An atom over the same sequence is not the tuple's cell: a cell for each.
    let a = Value::atom_with("p", vec![inner.clone()]);
    let both = Value::tuple(vec![inner.clone(), a.clone(), inner.clone(), a]);
    let mut h = Heap::new();
    let w = h.fresh(&both).unwrap();
    // `both`, the inner tuple and its strings, and the atom. The inner tuple is reached three
    // times (twice in `both`, once in the atom) and the atom twice: three more references.
    assert_eq!((h.stats.allocations, h.stats.increments), (5, 3));
    assert_eq!(h.value(w).unwrap(), both);
    h.dec(w).unwrap();
    assert_eq!(h.live(), 0);
    // Equal sequences built apart are cells of their own.
    let apart = Value::tuple(vec![
        Value::tuple(vec![Value::Int(1), Value::Int(2)]),
        Value::tuple(vec![Value::Int(1), Value::Int(2)]),
    ]);
    let mut h = Heap::new();
    h.fresh(&apart).unwrap();
    assert_eq!((h.stats.allocations, h.stats.increments), (3, 0));
}

#[test]
fn a_cell_read_once_keeps_its_value_so_a_second_read_reads_one_word() {
    let mut h = Heap::new();
    let a = h.alloc(Obj::Str("a".into()));
    let w = h.alloc(Obj::Tuple(vec![a, Word::int(1)].into()));
    assert_eq!(
        h.value(w).unwrap(),
        Value::tuple(vec![Value::str("a"), Value::Int(1)])
    );
    assert_eq!(h.stats.converted, 3, "the tuple and its two parts");
    assert_eq!(
        h.value(w).unwrap(),
        Value::tuple(vec![Value::str("a"), Value::Int(1)])
    );
    assert_eq!(h.stats.converted, 4, "the tuple alone");
    // An atom cell the same way, its name and field names kept; it holds `a` too.
    h.inc(a).unwrap();
    let x = h.alloc(Obj::Atom {
        name: "err".into(),
        fields: vec![Arc::from("code"), "msg".into()].into(),
        args: [Word::int(3), a].into(),
    });
    let code_a = Value::atom_named(
        "err",
        vec![
            ("code".into(), Value::Int(3)),
            ("msg".into(), Value::str("a")),
        ],
    )
    .expect("no repeated field");
    assert_eq!(h.value(x).unwrap(), code_a);
    assert_eq!(h.value(x).unwrap(), code_a);
    // A fresh value is kept from the start.
    let before = h.stats.converted;
    let f = h.fresh(&err_struct()).unwrap();
    assert_eq!(h.value(f).unwrap(), err_struct());
    assert_eq!(h.stats.converted, before + 1);
    // A freed cell keeps nothing: its slot taken again holds the new value.
    h.dec(w).unwrap();
    let y = h.alloc(Obj::Tuple(vec![Word::int(9)].into()));
    assert_eq!(y.index(), w.index());
    assert_eq!(h.value(y).unwrap(), Value::tuple(vec![Value::Int(9)]));
}

#[test]
fn reading_a_word_that_is_no_data_value_is_a_bug_in_zedc() {
    let mut h = Heap::new();
    let clo = h.alloc(Obj::Clo {
        lambda: 0,
        caps: Box::new([]),
    });
    assert_eq!(h.value(clo).unwrap_err(), closure_as_data());
    let inside = h.alloc(Obj::Tuple(vec![clo, Word::int(1)].into()));
    assert_eq!(h.value(inside).unwrap_err(), closure_as_data());
    for tag in [Word::PRIM, Word::SOURCE, Word::STATE, Word::ERR] {
        let w = Word { tag, bits: 0 };
        assert_eq!(h.value(w).unwrap_err(), not_data(tag), "tag {tag}");
    }
    assert!(not_data(7).contains("a word tagged 7 was read as data"));
    assert!(closure_as_data().contains("treated a function as a data value"));
}

#[test]
fn functions_are_closures_primitives_and_lookup_ports() {
    let mut h = Heap::new();
    let clo = h.alloc(Obj::Clo {
        lambda: 2,
        caps: [Word::int(5)].into(),
    });
    let s = h.alloc(Obj::Str("s".into()));
    let k = h.uncounted(Value::atom("e"));
    for (w, f) in [
        (
            Word {
                tag: Word::PRIM,
                bits: 3,
            },
            true,
        ),
        (
            Word {
                tag: Word::SOURCE,
                bits: 0,
            },
            true,
        ),
        (clo, true),
        (s, false),
        (k, false),
        (Word::int(1), false),
        (Word::state(), false),
        (Word::err(), false),
    ] {
        assert_eq!(h.is_function(w).unwrap(), f, "{w:?}");
    }
    h.dec(clo).unwrap();
    assert_eq!(
        h.is_function(clo).unwrap_err(),
        freed(Freed::Used, clo.index())
    );
}

#[test]
fn a_capture_is_read_from_a_closure_and_from_nothing_else() {
    let mut h = Heap::new();
    let s = h.alloc(Obj::Str("cap".into()));
    let clo = h.alloc(Obj::Clo {
        lambda: 0,
        caps: [Word::int(5), s].into(),
    });
    assert_eq!(h.capture(clo, 0).unwrap(), Word::int(5));
    assert_eq!(h.capture(clo, 1).unwrap(), s);
    let not_clo = |tag: i64| {
        crate::bug::bug(
            "called something that is not a function",
            &format!("a word tagged {tag} is not a closure"),
        )
    };
    assert_eq!(h.capture(s, 0).unwrap_err(), not_clo(Word::CELL));
    assert_eq!(h.capture(Word::int(1), 0).unwrap_err(), not_clo(Word::INT));
    // Dropping the closure drops its captures.
    h.dec(clo).unwrap();
    assert_eq!(h.live(), 0);
    assert_eq!(
        h.capture(clo, 0).unwrap_err(),
        freed(Freed::Used, clo.index())
    );
}

#[test]
fn a_count_write_on_a_word_that_is_no_cell_does_nothing() {
    let mut h = Heap::new();
    let k = h.uncounted(Value::tuple(vec![Value::Int(1)]));
    for w in [
        Word::int(1),
        Word::state(),
        Word::err(),
        Word {
            tag: Word::PRIM,
            bits: 0,
        },
        k,
    ] {
        h.inc(w).unwrap();
        h.dec(w).unwrap();
    }
    assert_eq!(h.stats, Stats::default());
}

#[test]
fn a_cell_is_counted_shared_once_per_generation() {
    let mut h = Heap::new();
    let w = h.alloc(Obj::Str("a".into()));
    h.inc(w).unwrap();
    h.inc(w).unwrap();
    assert_eq!((h.stats.increments, h.stats.shared), (2, 1));
    for _ in 0..3 {
        h.dec(w).unwrap();
    }
    assert_eq!(h.live(), 0);
    let v = h.alloc(Obj::Str("b".into()));
    assert_eq!(v.index(), w.index());
    h.inc(v).unwrap();
    assert_eq!(h.stats.shared, 2, "the next generation is shared anew");
    // A count back at 1 and up to 2 again in one generation is one shared cell.
    h.dec(v).unwrap();
    h.inc(v).unwrap();
    assert_eq!(h.stats.shared, 2);
}

#[test]
fn each_use_of_a_freed_cell_names_what_the_code_did() {
    let mut h = Heap::new();
    let w = h.alloc(Obj::Str("a".into()));
    h.dec(w).unwrap();
    assert_eq!(h.value(w).unwrap_err(), freed(Freed::Used, 0));
    assert_eq!(h.inc(w).unwrap_err(), freed(Freed::Shared, 0));
    assert_eq!(h.dec(w).unwrap_err(), freed(Freed::Dropped, 0));
    // The same for an old word of a cell taken again.
    let again = h.alloc(Obj::Str("b".into()));
    assert_eq!(again.index(), 0);
    assert_eq!(h.value(w).unwrap_err(), freed(Freed::Used, 0));
    assert_eq!(h.inc(w).unwrap_err(), freed(Freed::Shared, 0));
    assert_eq!(h.dec(w).unwrap_err(), freed(Freed::Dropped, 0));
    assert_eq!(h.value(again).unwrap(), Value::str("b"));
    for (how, what, did) in [
        (Freed::Used, "read a value after it had released", "read"),
        (
            Freed::Shared,
            "kept one more reference",
            "given a new reference",
        ),
        (Freed::Dropped, "released a value's memory twice", "dropped"),
    ] {
        let m = freed(how, 4);
        assert!(m.contains(what), "{m}");
        assert!(
            m.contains(&format!("the heap's cell 4 was {did} after it was freed")),
            "{m}"
        );
        assert!(
            m.starts_with("the program stopped because of a bug in zedc"),
            "{m}"
        );
    }
}

#[test]
fn a_bug_message_says_the_fault_is_zedcs_and_names_the_place() {
    let m = crate::bug::bug("did a thing", "place 7");
    assert_eq!(
        m,
        "the program stopped because of a bug in zedc, not in the program: the code zedc made \
         for the program did a thing. Please report it to the Zed developers with the \
         program's source, the input it was given, and this line: place 7"
    );
}

#[test]
fn dropping_a_closure_or_an_atom_drops_each_part_once() {
    let mut h = Heap::new();
    let s = h.alloc(Obj::Str("s".into()));
    h.inc(s).unwrap();
    let clo = h.alloc(Obj::Clo {
        lambda: 0,
        caps: [s, Word::int(1)].into(),
    });
    let atom = h.alloc(Obj::Atom {
        name: "a".into(),
        fields: Fields::default(),
        args: [s, clo].into(),
    });
    h.dec(atom).unwrap();
    assert_eq!(h.live(), 0, "the atom, the closure and the string");
    assert_eq!((h.stats.decrements, h.stats.frees), (4, 3));
}

#[test]
fn a_release_keeping_nothing_frees_a_cell_held_once_with_no_write_for_it() {
    let mut h = Heap::new();
    let v = Value::tuple(vec![Value::str("a"), Value::tuple(vec![Value::str("b")])]);
    let w = h.fresh(&v).unwrap();
    h.release(w, &Paths::default(), &[]).unwrap();
    // The root is freed without a write; its two parts are dropped, the inner tuple freeing
    // its string.
    assert_eq!((h.stats.decrements, h.live()), (3, 0));
    // A shared cell keeping nothing loses one reference.
    let mut h = Heap::new();
    let w = h.fresh(&v).unwrap();
    h.inc(w).unwrap();
    h.release(w, &Paths::default(), &[]).unwrap();
    assert_eq!((h.stats.decrements, h.live()), (1, 4));
    // A word that is no cell has nothing to release.
    h.release(Word::int(1), &Paths::default(), &[]).unwrap();
    let k = h.uncounted(v);
    h.release(k, &Paths::default(), &[]).unwrap();
    assert_eq!((h.stats.decrements, h.live()), (1, 4));
}

#[test]
fn a_release_keeping_the_whole_value_writes_nothing() {
    let mut h = Heap::new();
    let w = h
        .fresh(&Value::tuple(vec![Value::str("a"), Value::str("b")]))
        .unwrap();
    let before = h.stats;
    h.release(w, &Paths::default(), &[Paths::ROOT]).unwrap();
    assert_eq!((h.stats, h.live()), (before, 3));
}

#[test]
fn a_release_keeps_parts_at_every_depth_held_once_or_shared() {
    // (a, (b, c)) read by (x, (_, z)), keeping x and z.
    let v = Value::tuple(vec![
        Value::str("a"),
        Value::tuple(vec![Value::str("b"), Value::str("c")]),
    ]);
    let p = Pattern::Tuple(vec![
        bind("x"),
        Pattern::Tuple(vec![Pattern::Wild, bind("z")]),
    ]);
    for shared in [false, true] {
        let mut h = Heap::new();
        let w = h.fresh(&v).unwrap();
        if shared {
            h.inc(w).unwrap();
        }
        let mut paths = Paths::default();
        let mut out = Vec::new();
        assert!(h.matches(&p, w, &mut paths, &mut out).unwrap());
        let kept: Vec<usize> = out.iter().map(|&(_, n)| n).collect();
        assert_eq!(
            kept.iter().map(|&n| paths.path(n)).collect::<Vec<_>>(),
            vec![vec![0], vec![1, 1]]
        );
        let before = h.stats;
        h.release(w, &paths, &kept).unwrap();
        let (inc, dec) = (
            h.stats.increments - before.increments,
            h.stats.decrements - before.decrements,
        );
        if shared {
            // Each kept part gains a reference, the scrutinee loses one; nothing is freed.
            assert_eq!((inc, dec, h.live()), (2, 1, 5), "shared");
        } else {
            // The outer and inner tuples are freed with no write; `b` is dropped; a and c
            // move out.
            assert_eq!((inc, dec, h.live()), (0, 1, 2), "held once");
        }
        assert_eq!(h.value(out[0].0).unwrap(), Value::str("a"));
        assert_eq!(h.value(out[1].0).unwrap(), Value::str("c"));
    }
}

#[test]
fn a_kept_path_past_the_parts_of_a_cell_is_a_bug_in_zedc() {
    let mut h = Heap::new();
    let w = h
        .fresh(&Value::tuple(vec![Value::str("a"), Value::str("b")]))
        .unwrap();
    let (paths, end) = one_path(&[5]);
    assert_eq!(
        h.release(w, &paths, &[end]).unwrap_err(),
        crate::bug::bug(
            "released a value and kept a part of it that the value does not have",
            "a kept path reads part 5 of a cell of 2 parts"
        )
    );
    // On a shared cell the walk reads a freed or absent part the same way: a scalar has none.
    let mut h = Heap::new();
    let t = h.alloc(Obj::Tuple(vec![Word::int(1), Word::int(2)].into()));
    h.inc(t).unwrap();
    let (paths, end) = one_path(&[1, 0]);
    assert!(h.release(t, &paths, &[end]).is_err());
    // A freed scrutinee is a freed cell read.
    let mut h = Heap::new();
    let w = h.alloc(Obj::Tuple(vec![Word::int(1)].into()));
    h.dec(w).unwrap();
    assert_eq!(
        h.release(w, &Paths::default(), &[]).unwrap_err(),
        freed(Freed::Used, 0)
    );
}

#[test]
fn a_function_matches_only_a_wildcard_a_name_and_a_type_of_functions() {
    let mut h = Heap::new();
    let clo = h.alloc(Obj::Clo {
        lambda: 0,
        caps: Box::new([]),
    });
    let prim = Word {
        tag: Word::PRIM,
        bits: 1,
    };
    let port = Word {
        tag: Word::SOURCE,
        bits: 0,
    };
    for f in [clo, prim, port] {
        assert!(matched(&mut h, &Pattern::Wild, f).0, "{f:?} _");
        let (ok, binders, _) = matched(&mut h, &bind("f"), f);
        assert!(ok && binders == vec![(f, vec![])], "{f:?} f");
        assert!(
            matched(&mut h, &Pattern::Is(Type::top()), f).0,
            "{f:?} is _"
        );
        assert!(
            !matched(&mut h, &Pattern::Is(Type::int()), f).0,
            "{f:?} is int"
        );
        for p in [
            Pattern::Lit(Value::Int(0)),
            Pattern::AnyAtom,
            Pattern::Tuple(vec![]),
            Pattern::Atom("e".into(), vec![]),
            Pattern::Fields("e".into(), vec![("f".into(), Pattern::Wild)]),
        ] {
            assert!(!matched(&mut h, &p, f).0, "{f:?} {p:?}");
        }
    }
}

#[test]
fn a_literal_pattern_matches_an_equal_value_of_every_kind_and_form() {
    let mut h = Heap::new();
    let values = [
        Value::Int(-1),
        Value::Bool(true),
        Value::float(f64::NAN),
        Value::str("ab"),
        Value::str(""),
        big(),
        rat(1, 3),
        Value::tuple(vec![Value::Int(1), Value::str("x")]),
        Value::tuple(vec![Value::Int(1), Value::str("y")]),
        Value::tuple(vec![Value::Int(1)]),
        Value::tuple(vec![]),
        Value::atom("e"),
        Value::atom_with("e", vec![]),
        Value::atom_with("e", vec![Value::str("x")]),
        Value::atom_with("f", vec![Value::str("x")]),
        Value::atom_with("e", vec![Value::str("x"), Value::str("x")]),
        err_struct(),
        Value::atom_named("err", vec![("code".into(), Value::Int(3))]).unwrap(),
    ];
    // Each as a fresh word (cells where it boxes) and as a constant of the table.
    let mut words = Vec::new();
    for v in &values {
        words.push((h.fresh(v).unwrap(), v));
        words.push((h.uncounted(v.clone()), v));
    }
    for &(w, v) in &words {
        for l in &values {
            let ok = matched(&mut h, &Pattern::Lit(l.clone()), w).0;
            assert_eq!(ok, v == l, "{v:?} as {w:?} against literal {l:?}");
        }
    }
    // A string of the literal's length that differs, read to its first different byte.
    let w = h.fresh(&Value::str("ac")).unwrap();
    assert!(!matched(&mut h, &Pattern::Lit(Value::str("ab")), w).0);
    // A word that holds no value is a bug when matched against a literal.
    let mut out = Vec::new();
    assert_eq!(
        h.matches(
            &Pattern::Lit(Value::Int(0)),
            Word::state(),
            &mut Paths::default(),
            &mut out
        )
        .unwrap_err(),
        not_data(Word::STATE)
    );
}

#[test]
fn any_atom_matches_each_atom_and_nothing_else() {
    let mut h = Heap::new();
    for (v, atom) in [
        (Value::atom("e"), true),
        (Value::atom_with("e", vec![]), true),
        (Value::atom_with("e", vec![Value::str("x")]), true),
        (err_struct(), true),
        (Value::tuple(vec![Value::str("x")]), false),
        (Value::tuple(vec![]), false),
        (Value::str("e"), false),
        (Value::Int(1), false),
        (big(), false),
    ] {
        let fresh = h.fresh(&v).unwrap();
        let constant = h.uncounted(v.clone());
        assert_eq!(
            matched(&mut h, &Pattern::AnyAtom, fresh).0,
            atom,
            "{v:?} fresh"
        );
        assert_eq!(
            matched(&mut h, &Pattern::AnyAtom, constant).0,
            atom,
            "{v:?} constant"
        );
    }
}

#[test]
fn a_type_pattern_reads_a_cell_only_when_its_kind_alone_does_not_decide() {
    let mut h = Heap::new();
    let s = h.fresh(&Value::str("a")).unwrap();
    let t = h
        .fresh(&Value::tuple(vec![Value::Int(1), Value::Int(2)]))
        .unwrap();
    let a = h
        .fresh(&Value::atom_with("e", vec![Value::Int(1)]))
        .unwrap();
    let b = h.fresh(&big()).unwrap();
    let k = h.uncounted(Value::str("k"));
    let lit = |v: &str| Type::lit(&Value::str(v)).expect("a literal type");
    let ints2 = Type::tuple(vec![Type::int(), Type::int()]);
    let cases = [
        (s, Type::string(), true),
        (s, Type::int(), false),
        (s, lit("a"), true),
        (s, lit("b"), false),
        (t, Type::universe(Universe::Tuple), true),
        (t, Type::string(), false),
        (t, ints2.clone(), true),
        (t, Type::tuple(vec![Type::int()]), false),
        (a, Type::atom_with("e", &Type::top()), true),
        (a, Type::atom("e"), false),
        (
            a,
            Type::atom_with("e", &Type::tuple(vec![Type::int()])),
            true,
        ),
        (
            a,
            Type::atom_with("e", &Type::tuple(vec![Type::string()])),
            false,
        ),
        (a, Type::atom_with("f", &Type::top()), false),
        (b, Type::int(), true),
        (b, Type::rat(), false),
        (k, Type::string(), true),
        (k, lit("k"), true),
        (k, Type::int(), false),
        (Word::int(3), Type::int(), true),
        (Word::int(3), Type::string(), false),
        (
            Word::scalar(&Value::Bool(true)).unwrap(),
            Type::bool(),
            true,
        ),
    ];
    for (w, ty, is) in cases {
        let before = h.stats.converted;
        assert_eq!(
            matched(&mut h, &Pattern::Is(ty.clone()), w).0,
            is,
            "{w:?} is {ty:?}"
        );
        // A string or tuple whose kind `t` holds whole or not at all is not read.
        if w == s && (ty == Type::string() || ty == Type::int()) {
            assert_eq!(h.stats.converted, before, "{ty:?} decided by the kind");
        }
    }
    assert_eq!(
        h.matches(
            &Pattern::Is(Type::int()),
            Word::state(),
            &mut Paths::default(),
            &mut Vec::new()
        )
        .unwrap_err(),
        not_data(Word::STATE)
    );
}

#[test]
fn an_atom_pattern_needs_the_name_a_tuple_payload_of_its_length_and_its_bareness() {
    let mut h = Heap::new();
    let one = Value::atom_with("some", vec![Value::str("x")]);
    let p1 = Pattern::Atom("some".into(), vec![bind("v")]);
    for (v, p, ok) in [
        (one.clone(), p1.clone(), true),
        (
            one.clone(),
            Pattern::Atom("none".into(), vec![bind("v")]),
            false,
        ),
        (one.clone(), Pattern::Atom("some".into(), vec![]), false),
        (
            one.clone(),
            Pattern::Atom("some".into(), vec![bind("v"), bind("w")]),
            false,
        ),
        (Value::atom("some"), p1.clone(), false),
        (
            Value::atom("some"),
            Pattern::Atom("some".into(), vec![]),
            true,
        ),
        (
            Value::atom_with("some", vec![]),
            Pattern::Atom("some".into(), vec![]),
            false,
        ),
        (
            Value::atom_named("some", vec![("v".into(), Value::str("x"))]).unwrap(),
            p1.clone(),
            false,
        ),
        (Value::tuple(vec![Value::str("x")]), p1.clone(), false),
        (Value::str("some"), p1.clone(), false),
    ] {
        let fresh = h.fresh(&v).unwrap();
        let constant = h.uncounted(v.clone());
        assert_eq!(
            matched(&mut h, &p, fresh).0,
            ok,
            "{v:?} fresh against {p:?}"
        );
        assert_eq!(
            matched(&mut h, &p, constant).0,
            ok,
            "{v:?} constant against {p:?}"
        );
    }
    // The binder gets the part's word: the string's cell, or for a constant its table entry.
    let w = h.fresh(&one).unwrap();
    let (_, binders, entered) = matched(&mut h, &p1, w);
    assert_eq!(binders.len(), 1);
    assert_eq!(binders[0].1, vec![0]);
    assert_eq!(entered, 1);
    assert_eq!(h.value(binders[0].0).unwrap(), Value::str("x"));
}

#[test]
fn a_field_pattern_reads_named_fields_of_a_struct_payload_in_any_order() {
    let mut h = Heap::new();
    let v = err_struct();
    let fresh = h.fresh(&v).unwrap();
    let constant = h.uncounted(v.clone());
    let fields = |fs: &[(&str, Pattern)]| -> Vec<(Arc<str>, Pattern)> {
        fs.iter().map(|(f, p)| (Arc::from(*f), p.clone())).collect()
    };
    for w in [fresh, constant] {
        // Fields named in another order than sorted, and a subset.
        let p = Pattern::Fields(
            "err".into(),
            fields(&[("msg", bind("m")), ("code", bind("c"))]),
        );
        let (ok, binders, _) = matched(&mut h, &p, w);
        assert!(ok, "{w:?}");
        // `code` is part 0 and `msg` part 1 in name order.
        assert_eq!(binders[0].1, vec![1]);
        assert_eq!(binders[1].1, vec![0]);
        assert_eq!(h.value(binders[0].0).unwrap(), Value::str("x"));
        assert_eq!(binders[1].0, Word::int(3));
        let sub = Pattern::Fields(
            "err".into(),
            fields(&[("code", Pattern::Lit(Value::Int(3)))]),
        );
        assert!(matched(&mut h, &sub, w).0, "a subset of the fields");
        let wrong = Pattern::Fields(
            "err".into(),
            fields(&[("code", Pattern::Lit(Value::Int(4)))]),
        );
        assert!(!matched(&mut h, &wrong, w).0, "a field's value differs");
        let missing = Pattern::Fields(
            "err".into(),
            fields(&[("code", Pattern::Wild), ("zz", Pattern::Wild)]),
        );
        assert!(
            !matched(&mut h, &missing, w).0,
            "a field the payload does not have"
        );
        let name = Pattern::Fields("bad".into(), fields(&[("code", Pattern::Wild)]));
        assert!(!matched(&mut h, &name, w).0, "another name");
        let positional = Pattern::Atom("err".into(), vec![Pattern::Wild, Pattern::Wild]);
        assert!(
            !matched(&mut h, &positional, w).0,
            "a struct payload has no positions"
        );
    }
    // A tuple payload has no field names.
    let t = h
        .fresh(&Value::atom_with("err", vec![Value::Int(3)]))
        .unwrap();
    let p = Pattern::Fields("err".into(), fields(&[("code", Pattern::Wild)]));
    assert!(!matched(&mut h, &p, t).0);
}

#[test]
fn a_tuple_pattern_needs_a_tuple_of_its_length_and_enters_each_part_it_reads() {
    let mut h = Heap::new();
    let v = Value::tuple(vec![
        Value::Int(1),
        Value::str("s"),
        Value::tuple(vec![Value::Int(2)]),
    ]);
    let fresh = h.fresh(&v).unwrap();
    let constant = h.uncounted(v.clone());
    let p = Pattern::Tuple(vec![
        Pattern::Lit(Value::Int(1)),
        bind("s"),
        Pattern::Tuple(vec![bind("n")]),
    ]);
    for w in [fresh, constant] {
        let (ok, binders, entered) = matched(&mut h, &p, w);
        assert!(ok);
        assert_eq!(entered, 4, "three parts and the inner part");
        assert_eq!(
            binders.iter().map(|b| b.1.clone()).collect::<Vec<_>>(),
            vec![vec![1], vec![2, 0]]
        );
        assert_eq!(binders[1].0, Word::int(2), "a scalar part is its word");
        assert_eq!(h.value(binders[0].0).unwrap(), Value::str("s"));
        // A failure at the second part leaves the nodes entered before it.
        let q = Pattern::Tuple(vec![
            Pattern::Wild,
            Pattern::Lit(Value::str("t")),
            Pattern::Wild,
        ]);
        let (ok, _, entered) = matched(&mut h, &q, w);
        assert!(!ok);
        assert_eq!(entered, 2);
        for q in [
            Pattern::Tuple(vec![Pattern::Wild, Pattern::Wild]),
            Pattern::Tuple(vec![]),
            Pattern::Atom(
                "t".into(),
                vec![Pattern::Wild, Pattern::Wild, Pattern::Wild],
            ),
        ] {
            assert!(!matched(&mut h, &q, w).0, "{q:?}");
        }
    }
    // The empty tuple matches `()` alone; a string, a scalar and an atom match no tuple.
    let unit = h.fresh(&Value::tuple(vec![])).unwrap();
    assert!(matched(&mut h, &Pattern::Tuple(vec![]), unit).0);
    let s = h.uncounted(Value::str("s"));
    let a = h
        .fresh(&Value::atom_with("t", vec![Value::Int(1)]))
        .unwrap();
    for w in [s, a, Word::int(1)] {
        assert!(
            !matched(&mut h, &Pattern::Tuple(vec![Pattern::Wild]), w).0,
            "{w:?}"
        );
    }
}

#[test]
fn matching_a_constant_again_enters_its_parts_once() {
    let mut h = Heap::new();
    let k = h.uncounted(Value::tuple(vec![
        Value::tuple(vec![Value::Int(1), Value::Int(2)]),
        Value::str("s"),
    ]));
    let p = Pattern::Tuple(vec![
        Pattern::Tuple(vec![Pattern::Wild, bind("y")]),
        Pattern::Wild,
    ]);
    assert!(matched(&mut h, &p, k).0);
    let after_first = h.table_len();
    assert_eq!(
        after_first,
        1 + 2 + 2,
        "the entry, its two parts and the inner pair"
    );
    for _ in 0..3 {
        let (ok, binders, _) = matched(&mut h, &p, k);
        assert!(ok);
        assert_eq!(binders[0].0, Word::int(2));
    }
    assert_eq!(h.table_len(), after_first);
}

#[test]
fn nested_patterns_bind_in_preorder_at_every_depth() {
    let mut h = Heap::new();
    let v = Value::atom_with(
        "n",
        vec![Value::tuple(vec![
            Value::Int(1),
            Value::atom_with("n", vec![Value::Int(2)]),
        ])],
    );
    let p = Pattern::Atom(
        "n".into(),
        vec![Pattern::Tuple(vec![
            bind("a"),
            Pattern::Atom("n".into(), vec![bind("b")]),
        ])],
    );
    for w in [h.fresh(&v).unwrap(), h.uncounted(v.clone())] {
        let (ok, binders, entered) = matched(&mut h, &p, w);
        assert!(ok);
        assert_eq!(
            binders,
            vec![(Word::int(1), vec![0, 0]), (Word::int(2), vec![0, 1, 0])]
        );
        assert_eq!(entered, 4);
    }
}

#[cfg(feature = "counts")]
#[test]
fn survivors_group_live_cells_by_kind_and_allocating_node() {
    let mut h = Heap::new();
    h.allocating(Some(4));
    h.fresh(&Value::str("a")).unwrap();
    h.fresh(&Value::str("b")).unwrap();
    h.fresh(&big()).unwrap();
    h.allocating(None);
    h.fresh(&Value::tuple(vec![Value::Int(1)])).unwrap();
    h.fresh(&Value::atom_with("e", vec![Value::Int(1)]))
        .unwrap();
    h.fresh(&rat(1, 2)).unwrap();
    h.fresh(&Value::path(vec![Value::Int(1)])).unwrap();
    h.fresh(&Value::Family(Family::new())).unwrap();
    h.fresh(&Value::float32(1.0)).unwrap();
    h.alloc(Obj::Clo {
        lambda: 0,
        caps: Box::new([]),
    });
    let gone = h.fresh(&Value::str("gone")).unwrap();
    h.dec(gone).unwrap();
    let s = |kind, node, cells| Survivor { kind, node, cells };
    assert_eq!(
        h.survivors(),
        vec![
            s("String", Some(4), 2),
            s("atom", None, 1),
            s("closure", None, 1),
            s("family", None, 1),
            s("int", Some(4), 1),
            s("kernel value", None, 1),
            s("keypath", None, 1),
            s("rat", None, 1),
            s("tuple", None, 1),
        ]
    );
    // A cell taken again takes the node allocating now.
    h.allocating(Some(9));
    h.fresh(&Value::str("again")).unwrap();
    assert!(h.survivors().contains(&s("String", Some(9), 1)));
    // An integer held as a kernel value in a cell is an int.
    h.alloc(Obj::Data(Box::new(Value::Int(1))));
    assert!(h.survivors().contains(&s("int", Some(9), 1)));
}

#[cfg(feature = "counts")]
#[test]
fn releases_are_recorded_in_order_only_once_asked_for() {
    let mut h = Heap::new();
    let w = h.fresh(&Value::str("before")).unwrap();
    h.dec(w).unwrap();
    assert_eq!(
        h.released(),
        vec![],
        "nothing is recorded before it is asked for"
    );
    h.record_releases();
    h.record_releases();
    let w = h
        .fresh(&Value::tuple(vec![Value::str("a"), big(), Value::str("b")]))
        .unwrap();
    h.dec(w).unwrap();
    let r = |kind, text: Option<&str>| Released {
        kind,
        text: text.map(Text::from),
    };
    assert_eq!(
        h.released(),
        vec![
            r("tuple", None),
            r("String", Some("a")),
            r("int", None),
            r("String", Some("b")),
        ]
    );
    assert_eq!(h.released(), vec![], "taken out of the record");
    let w = h.fresh(&Value::str("c")).unwrap();
    h.dec(w).unwrap();
    assert_eq!(
        h.released(),
        vec![r("String", Some("c"))],
        "still recording"
    );
}

#[test]
fn comparing_a_closure_with_a_literal_is_a_bug_in_zedc() {
    // The checker never compares a function with a value (functions have no equality), so a
    // closure reached by a literal pattern is code zedc should not have made.
    let mut h = Heap::new();
    let clo = h.alloc(Obj::Clo {
        lambda: 0,
        caps: Box::new([]),
    });
    let t = h.alloc(Obj::Tuple(vec![clo, Word::int(1)].into()));
    let lit = Pattern::Lit(Value::tuple(vec![Value::Int(0), Value::Int(1)]));
    assert_eq!(
        h.matches(&lit, t, &mut Paths::default(), &mut Vec::new())
            .unwrap_err(),
        closure_as_data()
    );
}
