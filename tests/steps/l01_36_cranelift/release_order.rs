//! Release follows the counts of the data graph, never a stack (DESIGN.md sec:memory,
//! "Release follows the counts of the data graph"; plan row SPEC-release-dag): a value is
//! freed at its last use, so a value read only early is freed before a value made after it on
//! another branch and held to the end, and a tuple is freed before its parts. Each test runs
//! natively with the heap's record of the cells it frees, in order (feature `counts`), on the
//! plan with fusion and on the one without.

use zed_kernel::term::build::{app, lam, let_, lit, prim, var};
use zed_kernel::{Evaluator, Prim, Term, Text, Value, World};
use zed_rt::{Heap, Obj, Parts, Released, Word};
use zedc::zir::lower::lower;
use zedc::zir::memory::{self, Plan};

use super::kernel;

/// The strings `t` frees, in the order it frees them, run natively on the plan with fusion
/// `fuse`; `None` stands for a cell that is not a string. The value is checked against the
/// kernel's.
fn freed(t: &Term, fuse: bool) -> Vec<Option<String>> {
    let g = zed_native::legalize(lower(t).unwrap_or_else(|e| panic!("{e}")));
    let p = memory::plan(g.graph(), fuse);
    freed_on(t, &g, &p)
}

fn freed_on(t: &Term, g: &zedc::zir::legalize::Legalized, p: &Plan) -> Vec<Option<String>> {
    zed_native::record_releases(true);
    let _ = zed_native::counted();
    let o = zed_native::run(g, p, &mut Evaluator::new(World::new()));
    zed_native::record_releases(false);
    let o = o.unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(o.value, kernel(t).unwrap());
    let mut c = zed_native::counted();
    assert_eq!(c.runs, 1);
    assert!(c.left.is_empty(), "{:?}", c.left);
    c.released
        .pop()
        .unwrap()
        .into_iter()
        .map(|r| r.text.map(|t| t.flat().into_owned()))
        .collect()
}

/// Where the string `s` is freed in `order`; it is freed exactly once.
fn at(order: &[Option<String>], s: &str) -> usize {
    let hits: Vec<usize> = (0..order.len())
        .filter(|&i| order[i].as_deref() == Some(s))
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "`{s}` freed {} times in {order:?}",
        hits.len()
    );
    hits[0]
}

fn cat(a: Term, b: Term) -> Term {
    prim(Prim::Concat, vec![a, b])
}

fn len(a: Term) -> Term {
    prim(Prim::Len, vec![a])
}

/// The spec's `page`, its result read further by the caller: `header` is made first, `body`
/// after it on a branch that does not read it, `header`'s last use is `width`, and `body` is
/// read after that, to the end.
///
/// ```text
/// (name, text) -> {
///   header = "Report for " ++ name;
///   body = text ++ "\n" ++ text;
///   width = header.len;
///   (width, (body ++ "!").len)
/// }
/// ```
fn page() -> Term {
    let f = lam(
        &["name", "text"],
        let_(
            "header",
            cat(lit("Report for "), var("name")),
            let_(
                "body",
                cat(cat(var("text"), lit("\n")), var("text")),
                let_(
                    "width",
                    len(var("header")),
                    prim(
                        Prim::Tuple,
                        vec![var("width"), len(cat(var("body"), lit("!")))],
                    ),
                ),
            ),
        ),
    );
    app(f, vec![lit("Ann"), lit("lines")])
}

#[test]
fn a_value_read_early_is_freed_before_a_later_value_held_long() {
    for fuse in [true, false] {
        let order = freed(&page(), fuse);
        // A stack frees the inner `body` first and the outer `header` after it.
        let header = at(&order, "Report for Ann");
        let body = at(&order, "lines\nlines");
        assert!(header < body, "fuse {fuse}: {order:?}");
        // `body ++ "!"` is made after `header`'s last use and read once, by `len`.
        assert!(
            header < at(&order, "lines\nlines!"),
            "fuse {fuse}: {order:?}"
        );
    }
}

#[test]
fn a_value_returned_and_held_by_the_caller_is_freed_after_the_callee_frees_its_own() {
    // `page` returns `body`; the caller reads it after the call. `header` is freed in `page`.
    let f = lam(
        &["name", "text"],
        let_(
            "header",
            cat(lit("Report for "), var("name")),
            let_(
                "body",
                cat(cat(var("text"), lit("\n")), var("text")),
                prim(Prim::Tuple, vec![len(var("header")), var("body")]),
            ),
        ),
    );
    let t = let_(
        "r",
        app(f, vec![lit("Ann"), lit("lines")]),
        let_(
            "late",
            cat(lit("late "), lit("value")),
            prim(Prim::Tuple, vec![var("r"), len(var("late"))]),
        ),
    );
    for fuse in [true, false] {
        let order = freed(&t, fuse);
        let header = at(&order, "Report for Ann");
        assert!(header < at(&order, "late value"), "fuse {fuse}: {order:?}");
        assert!(
            header < at(&order, "lines\nlines"),
            "fuse {fuse}: {order:?}"
        );
        // `body` is part of the result, freed when the result is, at the very end.
        assert_eq!(
            at(&order, "lines\nlines"),
            order.len() - 1,
            "fuse {fuse}: {order:?}"
        );
    }
}

#[test]
fn a_tuple_is_freed_before_its_parts_and_its_parts_in_order() {
    // (("a" ++ "b", "c" ++ "d") as p; p's width): the tuple is dropped after `len` reads its
    // first part; LIFO holds along this path only: the tuple, then each part.
    let t = let_(
        "p",
        prim(
            Prim::Tuple,
            vec![cat(lit("a"), lit("b")), cat(lit("c"), lit("d"))],
        ),
        len(prim(Prim::TupleGet, vec![var("p"), lit(0)])),
    );
    for fuse in [true, false] {
        let order = freed(&t, fuse);
        let tuple = order.iter().position(Option::is_none).unwrap();
        assert!(tuple < at(&order, "ab"), "fuse {fuse}: {order:?}");
        assert!(tuple < at(&order, "cd"), "fuse {fuse}: {order:?}");
    }
}

/// `n` values each read once early, then one held to the end:
/// `s -> { h0 = s ++ "0"; w0 = h0.len; ...; body = s ++ s; (w0 + ... , (body ++ "!").len) }`,
/// in which every `hi` is freed before `body` is made.
pub(crate) fn many(n: usize) -> Term {
    let mut sum = lit(Value::Int(0));
    for i in 0..n {
        sum = prim(Prim::Add, vec![sum, var(&format!("w{i}"))]);
    }
    let mut body = let_(
        "body",
        cat(var("s"), var("s")),
        prim(Prim::Tuple, vec![sum, len(cat(var("body"), lit("!")))]),
    );
    for i in (0..n).rev() {
        body = let_(
            &format!("h{i}"),
            cat(var("s"), lit(i.to_string().as_str())),
            let_(&format!("w{i}"), len(var(&format!("h{i}"))), body),
        );
    }
    app(lam(&["s"], body), vec![lit("x")])
}

#[test]
fn many_early_values_are_each_freed_before_the_later_one() {
    let order = freed(&many(50), true);
    let body = at(&order, "xx");
    for i in 0..50 {
        assert!(at(&order, &format!("x{i}")) < body, "{order:?}");
    }
}

/// `n` tuples of two strings, made in order and dropped in order, the heap recording what it
/// frees: each tuple, then its parts, first to last, so the first made is the first freed.
pub(crate) fn tuples_dropped(texts: &[(Text, Text)]) -> Vec<Released> {
    let mut h = Heap::new();
    h.record_releases();
    let ws: Vec<Word> = texts
        .iter()
        .map(|(a, b)| {
            let a = h.alloc(Obj::Str(a.clone()));
            let b = h.alloc(Obj::Str(b.clone()));
            h.alloc(Obj::Tuple(Parts::from(vec![a, b])))
        })
        .collect();
    for w in ws {
        h.dec(w).unwrap();
    }
    assert_eq!(h.live(), 0);
    h.released()
}

pub(crate) fn texts(n: usize) -> Vec<(Text, Text)> {
    (0..n)
        .map(|i| (Text::from(format!("a{i}")), Text::from(format!("b{i}"))))
        .collect()
}

#[test]
fn the_heap_frees_in_the_order_the_counts_reach_zero() {
    let order = tuples_dropped(&texts(3));
    let names: Vec<String> = order
        .iter()
        .map(|r| {
            r.text
                .as_ref()
                .map_or_else(|| r.kind.into(), |t| t.flat().into_owned())
        })
        .collect();
    assert_eq!(
        names,
        [
            "tuple", "a0", "b0", "tuple", "a1", "b1", "tuple", "a2", "b2"
        ],
        "{order:?}"
    );
}
