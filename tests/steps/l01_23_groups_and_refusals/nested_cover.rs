//! `Searching::nested_cover` (row TEST-nested-cover-verdict-change) against the path without it.
//! DESIGN.md sec. L1.23 (emptiness of a box) takes out of the box each piece of a component cut
//! by one open tuple type on which narrowing proves the part empty, then splits the box into
//! its meet with each open tuple type, and counts a box none of its steps settles as
//! inhabited. `nested_cover` cuts only cells pairwise nested or disjoint and takes their
//! pieces out one after another, innermost first, each on the box as it stands, as DESIGN's
//! taking out does; without it, `take_out_piece` takes out one cell's piece at a time
//! (TEST-may-cover-piece-removal). So a verdict may change only from a refusal to `Empty` on
//! such a box, and every verdict either path gives must agree with enumerating the values.

use zed_kernel::Value;
use zed_kernel::types::{Refusal, Type, Verdict};
use zed_tests::instances::Rng;

/// The literals `0..VALUES` stand for a component's values; one more value, outside every
/// literal, stands for the rest of `top`, which a cell holds only when it is `top`.
const VALUES: usize = 3;
const TOP: u8 = (1 << (VALUES + 1)) - 1;
const LITERALS: u8 = (1 << VALUES) - 1;

fn cell_ty(m: u8) -> Type {
    if m == TOP {
        return Type::top();
    }
    Type::union_all(
        (0..VALUES)
            .filter(|&v| m & (1 << v) != 0)
            .map(|v| Type::lit(&Value::Int(v as i64)).expect("an integer literal")),
    )
}

fn cell_holds(m: u8, v: usize) -> bool {
    m == TOP || v < VALUES && m & (1 << v) != 0
}

/// A Boolean combination of tuple types of literal sets, which `holds` evaluates on one tuple.
#[derive(Clone, Debug)]
enum F {
    Row(Vec<u8>),
    Or(Box<F>, Box<F>),
    And(Box<F>, Box<F>),
    Less(Box<F>, Box<F>),
}

impl F {
    fn ty(&self) -> Type {
        match self {
            F::Row(r) => Type::tuple(r.iter().map(|&m| cell_ty(m)).collect()),
            F::Or(x, y) => &x.ty() | &y.ty(),
            F::And(x, y) => &x.ty() & &y.ty(),
            F::Less(x, y) => &x.ty() - &y.ty(),
        }
    }

    fn holds(&self, p: &[usize]) -> bool {
        match self {
            F::Row(r) => r.iter().zip(p).all(|(&m, &v)| cell_holds(m, v)),
            F::Or(x, y) => x.holds(p) || y.holds(p),
            F::And(x, y) => x.holds(p) && y.holds(p),
            F::Less(x, y) => x.holds(p) && !y.holds(p),
        }
    }

    fn less(self, y: F) -> F {
        F::Less(Box::new(self), Box::new(y))
    }
}

/// Whether some tuple of `width` values, each a literal or the rest, satisfies `f`.
fn inhabited(f: &F, width: usize) -> bool {
    (0..(VALUES + 1).pow(width as u32)).any(|mut i| {
        let p: Vec<usize> = (0..width)
            .map(|_| {
                let v = i % (VALUES + 1);
                i /= VALUES + 1;
                v
            })
            .collect();
        f.holds(&p)
    })
}

fn cell(g: &mut Rng) -> u8 {
    if g.below(6) == 0 {
        TOP
    } else {
        (g.below(LITERALS as usize) + 1) as u8
    }
}

fn row(g: &mut Rng, width: usize) -> F {
    F::Row((0..width).map(|_| cell(g)).collect())
}

fn rows(g: &mut Rng, width: usize, k: usize) -> F {
    (1..k).fold(row(g, width), |u, _| {
        F::Or(Box::new(u), Box::new(row(g, width)))
    })
}

fn random(g: &mut Rng, width: usize, depth: usize) -> F {
    let sub = |g: &mut Rng| Box::new(random(g, width, depth - 1));
    match if depth == 0 { 0 } else { g.below(5) } {
        0 | 1 => row(g, width),
        2 => F::Or(sub(g), sub(g)),
        3 => F::And(sub(g), sub(g)),
        _ => F::Less(sub(g), sub(g)),
    }
}

/// The verdict without `nested_cover` and with it, each from no kept results.
fn both(t: &Type) -> (Verdict, Verdict) {
    let old = Type::without_nested_cover(|| t.verdict());
    Type::forget_emptiness();
    let new = t.verdict();
    Type::forget_emptiness();
    (old, new)
}

fn class(v: Verdict) -> usize {
    match v {
        Verdict::Empty => 0,
        Verdict::Inhabited => 1,
        Verdict::Refused(_) => 2,
    }
}

/// Random boxes of widths 2 to 4 met with three kinds of part: any combination, the box less
/// rows of literal cells (the shape of `refusals::box_cover`), and rows less rows. Each
/// decided verdict on either path agrees with enumeration; a verdict that changes changes from
/// a refusal to `Empty`; and deciding the same types again with every result kept (a batch)
/// gives the verdicts each gave alone. The table of old against new verdicts is printed.
#[test]
fn both_paths_agree_with_enumeration_on_random_boxes() {
    zed_tests::deep::on_small_stack(|| {
        let (mut g, _) = Rng::fresh("nested cover against the old split");
        let mut table = [[0usize; 3]; 3];
        let mut drawn = Vec::new();
        for width in 2..=4 {
            for _ in 0..1000 {
                let inner = match g.below(3) {
                    0 => random(&mut g, width, 4),
                    1 => {
                        let lits = |g: &mut Rng| {
                            F::Row((0..width).map(|_| (g.below(7) + 1) as u8).collect())
                        };
                        let c = 4 + g.below(8);
                        (0..c).fold(F::Row(vec![LITERALS; width]), |t, _| t.less(lits(&mut g)))
                    }
                    _ => {
                        let (a, c) = (1 + g.below(4), 3 + g.below(9));
                        rows(&mut g, width, a).less(rows(&mut g, width, c))
                    }
                };
                let f = F::And(Box::new(row(&mut g, width)), Box::new(inner));
                let t = f.ty();
                let truth = inhabited(&f, width);
                let (old, new) = both(&t);
                for v in [old, new] {
                    if class(v) < 2 {
                        assert_eq!(class(v) == 1, truth, "{f:?}: old {old:?}, new {new:?}");
                    }
                }
                assert!(
                    old == new || matches!(old, Verdict::Refused(_)) && new == Verdict::Empty,
                    "{f:?}: old {old:?}, new {new:?}"
                );
                table[class(old)][class(new)] += 1;
                if old != new {
                    println!("changed from {old:?} to {new:?}: {f:?}");
                }
                drawn.push((t, new));
            }
        }
        for (t, alone) in &drawn {
            assert_eq!(t.verdict(), *alone, "{t:?} in a batch");
        }
        Type::forget_emptiness();
        let changed =
            table.iter().flatten().sum::<usize>() - (0..3).map(|i| table[i][i]).sum::<usize>();
        println!(
            "old verdict (rows) against new (columns), Empty, Inhabited, Refused: {table:?}; {changed} changed"
        );
    });
}

/// Component 0 cut by three cells that cross pairwise, `0 | 1`, `1 | 2` and `0 | 2`. Each
/// value lies in two of them, so the part is empty, which only the pieces `0`, `1` and `2`
/// show; no cell's own piece does. `nested_cover` leaves such a box to the split into the meet
/// with each open tuple type, which settles it on both paths.
#[test]
fn crossing_cells_are_left_to_the_split() {
    zed_tests::deep::on_small_stack(|| {
        let xor = |x: F, y: F| F::Or(Box::new(x.clone().less(y.clone())), Box::new(y.less(x)));
        let three = |second: [u8; 3], wide: u8| {
            let [a, b, c] = second;
            let odd = xor(
                xor(F::Row(vec![3, a]), F::Row(vec![6, b])),
                F::Row(vec![5, c]),
            );
            F::And(Box::new(F::Row(vec![TOP, wide])), Box::new(odd))
        };
        let less_three = F::Row(vec![LITERALS, LITERALS])
            .less(F::Row(vec![3, 3]))
            .less(F::Row(vec![6, 6]))
            .less(F::Row(vec![5, 5]));
        for (f, truth) in [
            (three([TOP; 3], TOP), false),
            (three([3; 3], 3), false),
            (three([3, 5, 6], TOP), true),
            (less_three, false),
        ] {
            let (old, new) = both(&f.ty());
            let want = if truth {
                Verdict::Inhabited
            } else {
                Verdict::Empty
            };
            assert_eq!((old, new), (want, want), "{f:?}");
            assert_eq!(inhabited(&f, 2), truth, "{f:?}");
        }
    });
}

/// The two kinds of box at the ends: nested cells (the small instance of the benchmark
/// `nested_sets_against_a_wider_second_component_are_decided_in_linear_time`), which both paths
/// decide, and `refusals::box_cover`, which only a split of two components at once settles
/// and which both refuse.
#[test]
fn nested_cells_are_decided_and_the_box_cover_refused_on_both_paths() {
    zed_tests::deep::on_small_stack(|| {
        use zedc::check::read::parse_type;
        let rows: Vec<String> = (0..4)
            .map(|i| format!("((#_, {i}) \\ (#a, {i}), 1)"))
            .collect();
        let left = parse_type(&rows.join(" | ")).unwrap();
        let right = parse_type("((#_, int), 1 | 2)").unwrap();
        let old = Type::without_nested_cover(|| left.subtype(&right));
        Type::forget_emptiness();
        assert!(old);
        assert!(left.subtype(&right));
        Type::forget_emptiness();
        let boxes: [[u8; 3]; 7] = [
            [3, 3, 3],
            [5, 5, 5],
            [6, 3, 5],
            [6, 4, 5],
            [4, 3, 6],
            [5, 6, 3],
            [3, 6, 6],
        ];
        let f = boxes
            .iter()
            .fold(F::Row(vec![LITERALS; 3]), |t, b| t.less(F::Row(b.to_vec())));
        let refused = Verdict::Refused(Refusal::TupleSplit);
        assert_eq!(both(&f.ty()), (refused, refused));
        assert!(!inhabited(&f, 3));
    });
}

/// A cell within `m`: each of its literals kept or dropped, and `top` kept or made its literals.
fn sub_cell(g: &mut Rng, m: u8) -> u8 {
    let lits = if m == TOP { LITERALS } else { m };
    let kept = (0..VALUES as u8)
        .filter(|&v| lits & (1 << v) != 0 && g.below(3) != 0)
        .fold(0, |s, v| s | (1 << v));
    if m == TOP && g.below(2) == 0 {
        TOP
    } else if kept == 0 {
        lits.isolate_lowest_one()
    } else {
        kept
    }
}

/// Random parts met with a box and with a box within it, each cell of the second within the
/// cell of the first (PROOF-narrow-tuples-monotone). Each decided verdict, on both paths,
/// agrees with enumeration. The proof at `Searching::nested_cover` does not rest on the
/// verdict of a box settling that of a box within it, so that is not asserted; the count of
/// draws where the box is decided `Empty` and the box within it is refused is printed.
#[test]
fn a_box_and_a_box_within_it_agree_with_enumeration() {
    zed_tests::deep::on_small_stack(|| {
        let (mut g, _) = Rng::fresh("a box and a box within it");
        let mut refused_within_empty = 0;
        let mut draws = 0;
        for width in 2..=3 {
            for _ in 0..600 {
                let part = random(&mut g, width, 4);
                let outer: Vec<u8> = (0..width).map(|_| cell(&mut g)).collect();
                let inner: Vec<u8> = outer.iter().map(|&m| sub_cell(&mut g, m)).collect();
                let mut verdicts = Vec::new();
                for b in [&outer, &inner] {
                    let f = F::And(Box::new(F::Row(b.clone())), Box::new(part.clone()));
                    let truth = inhabited(&f, width);
                    let (old, new) = both(&f.ty());
                    for v in [old, new] {
                        if class(v) < 2 {
                            assert_eq!(class(v) == 1, truth, "{f:?}: old {old:?}, new {new:?}");
                        }
                    }
                    verdicts.push(new);
                }
                draws += 1;
                if verdicts[0] == Verdict::Empty && matches!(verdicts[1], Verdict::Refused(_)) {
                    refused_within_empty += 1;
                }
            }
        }
        println!(
            "{refused_within_empty} of {draws} draws: the box Empty, the box within it refused"
        );
    });
}

/// The three crossing cells of `crossing_cells_are_left_to_the_split` on component 0, beside
/// `K = (_, 0 | 1)` on component 1, and a part `J` that narrowing alone shows empty wherever
/// component 1 is `2`. The box `(_, 0 | 1 | 2)` is settled by DESIGN.md L1.23 in two steps:
/// the piece `2` of component 1 (outside `K`) is taken out, since narrowing alone proves the
/// part empty there (`K` misses it, and `J` holds `(_, 2)` but not `(_, 1 | 2)`); on what is
/// left `K` holds the box, and the part is the odd count of the crossing cells, which no piece
/// settles and the split into the meet with each open tuple type does. Splitting the whole box
/// at once instead gives the piece of `K`, which is that box and cannot be split again on its
/// branch.
#[test]
fn a_piece_taken_out_before_the_split_leaves_a_box_the_split_settles() {
    zed_tests::deep::on_small_stack(|| {
        let xor = |x: F, y: F| F::Or(Box::new(x.clone().less(y.clone())), Box::new(y.less(x)));
        let odd = xor(
            xor(F::Row(vec![3, TOP]), F::Row(vec![6, TOP])),
            F::Row(vec![5, TOP]),
        );
        let j = F::And(
            Box::new(F::Row(vec![3, TOP])),
            Box::new(F::Row(vec![TOP, 4])),
        )
        .less(F::Row(vec![TOP, 6]));
        let f = F::And(
            Box::new(F::Row(vec![TOP, LITERALS])),
            Box::new(F::Or(
                Box::new(F::And(Box::new(F::Row(vec![TOP, 3])), Box::new(odd))),
                Box::new(j),
            )),
        );
        assert!(!inhabited(&f, 2));
        assert_eq!(both(&f.ty()), (Verdict::Empty, Verdict::Empty), "{f:?}");
    });
}

/// `nested_pieces` cuts the pieces one cell at a time only when a test of two cells is not
/// decided, which no small input makes. Here every call also cuts them so
/// (`Type::with_pieces_compared`): wherever the cells two at a time give pieces, those cut one
/// at a time are the same, and the verdict on the pieces cut one at a time is the verdict of
/// the ordinary path and agrees with enumeration. The random boxes of
/// `both_paths_agree_with_enumeration_on_random_boxes`, the crossing cells and the nested ones.
#[test]
fn pieces_cut_one_cell_at_a_time_are_those_found_two_at_a_time() {
    zed_tests::deep::on_small_stack(|| {
        use zedc::check::read::parse_type;
        let (mut g, _) = Rng::fresh("pieces cut one cell at a time");
        let mut fs = Vec::new();
        for width in 2..=4 {
            for _ in 0..300 {
                let inner = match g.below(2) {
                    0 => random(&mut g, width, 4),
                    _ => {
                        let (a, c) = (1 + g.below(4), 3 + g.below(9));
                        rows(&mut g, width, a).less(rows(&mut g, width, c))
                    }
                };
                fs.push((F::And(Box::new(row(&mut g, width)), Box::new(inner)), width));
            }
        }
        let xor = |x: F, y: F| F::Or(Box::new(x.clone().less(y.clone())), Box::new(y.less(x)));
        let odd = xor(
            xor(F::Row(vec![3, TOP]), F::Row(vec![6, TOP])),
            F::Row(vec![5, TOP]),
        );
        fs.push((F::And(Box::new(F::Row(vec![TOP, TOP])), Box::new(odd)), 2));
        let mut types: Vec<(Type, Option<bool>)> = fs
            .iter()
            .map(|(f, width)| (f.ty(), Some(inhabited(f, *width))))
            .collect();
        let rows: Vec<String> = (0..4)
            .map(|i| format!("((#_, {i}) \\ (#a, {i}), 1)"))
            .collect();
        let kernel = |s: &str| parse_type(s).unwrap().kernel().expect("a kernel type");
        let nested = &kernel(&rows.join(" | ")) - &kernel("((#_, int), 1 | 2)");
        types.push((nested, Some(false)));
        for (t, truth) in &types {
            let one = Type::with_pieces_compared(|| t.verdict());
            let two = t.verdict();
            Type::forget_emptiness();
            assert_eq!(one, two, "{t:?}");
            if class(one) < 2 {
                assert_eq!(Some(class(one) == 1), *truth, "{t:?}: {one:?}");
            }
        }
    });
}

/// Item TEST-kernel-unreached-paths-6: on component 0, the cell `1 | 2` comes after the
/// disjoint cells `0 | 1` and `2 | 3` and cuts both their pieces, so it crosses a cell before
/// it, and the cut one cell at a time stops at the second piece cut (its first `return None`)
/// and leaves the box to the steps below. Of ten boxes tried with these three cells, this was
/// the first to reach that line; the boxes less the three rows, such as
/// `(int, int) \ ((0 | 1, int) | (2 | 3, int) | (1 | 2, 1))`, did not. The value `(1, 1)` is
/// in the type.
#[test]
fn a_cell_that_cuts_two_pieces_stops_the_cut_one_cell_at_a_time() {
    zed_tests::deep::on_small_stack(|| {
        use zedc::check::read::parse_type;
        let s = "((0 | 1, 1) | (2 | 3, 2) | (1 | 2, 3)) \\ (0 | 3, 1 | 2 | 3)";
        let t = parse_type(s).unwrap().kernel().expect("a kernel type");
        let one = Type::with_pieces_compared(|| t.verdict());
        Type::forget_emptiness();
        let two = t.verdict();
        Type::forget_emptiness();
        assert_eq!(one, two, "{s}");
        assert_eq!(one, Verdict::Inhabited, "{s}");
    });
}
