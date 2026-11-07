//! Questions over shared conjunctions, decided from the answers of the conjunction each extends
//! (`presburger::extend`, LOAD-chain-share): each answer is the one `decide` gives the whole,
//! and a chain of n extensions is decided in time of its links.

use zedc::store::presburger::extend::{Answers, Extending};
use zedc::store::presburger::{Atom, Con, Formula, Lin, decide};

fn sym(name: &str) -> Lin {
    Lin::atom(Atom::Sym(name.into()))
}

/// `a >= b`.
fn ge(a: Lin, b: Lin) -> Formula {
    Formula::Con(Con::ge(&a, &b))
}

/// `part && rest`, with `part` kept whole, as the translator joins a call's relation.
fn extend(part: &Formula, rest: Vec<Formula>) -> Formula {
    let mut fs = vec![part.clone()];
    fs.extend(rest);
    Formula::and_keeping(fs, |i| i == 0)
}

/// The answers `decide` gives `f` and its negation.
fn decided(f: &Formula) -> Answers {
    Answers {
        holds: decide(f),
        fails: decide(&Formula::negate(f.clone())),
    }
}

/// `x + k * y <= c`.
fn sum(k: i64, c: i64) -> Formula {
    ge(Lin::constant(c), sym("x").plus(&sym("y").times(k)))
}

#[test]
fn each_answer_is_the_one_the_whole_has() {
    let (x, y) = (sym("x"), sym("y"));
    // A conjunction of two, so that it is kept whole and not one constraint.
    let base = Formula::and(vec![
        ge(x.clone(), y.clone()),
        ge(y.clone(), Lin::constant(0)),
    ]);
    // Holding everywhere: x >= 0 or x <= -1 with y in either of two halves, not seen as `true`
    // when it is built.
    let halves = |v: &Lin| {
        Formula::or(vec![
            ge(v.clone(), Lin::constant(0)),
            ge(Lin::constant(-1), v.clone()),
        ])
    };
    let everywhere = Formula::and(vec![halves(&x), halves(&y)]);
    let empty = Formula::and(vec![
        ge(x.clone(), Lin::constant(5)),
        ge(Lin::constant(4), x.clone()),
    ]);
    let cases = [
        // The point of the part serves.
        extend(&base, vec![ge(Lin::constant(100), x.clone())]),
        // The point of the part does not serve: decided whole.
        extend(
            &base,
            vec![
                ge(x.clone(), Lin::constant(50)),
                ge(y.clone(), Lin::constant(7)),
            ],
        ),
        // Nowhere, by the new parts alone.
        extend(&base, vec![ge(Lin::constant(-1), y.clone())]),
        // Nowhere, since the part holds nowhere.
        extend(&empty, vec![ge(x.clone(), Lin::constant(0))]),
        // The part holds everywhere: the negation is that of the new parts.
        extend(&everywhere, vec![ge(x.clone(), Lin::constant(3))]),
        extend(&everywhere, vec![]),
        // A part of a part.
        extend(&extend(&base, vec![sum(2, 40)]), vec![sum(3, 60)]),
        // No kept part, and not a conjunction.
        Formula::and(vec![ge(x.clone(), y.clone()), ge(y.clone(), x.clone())]),
        ge(x.clone(), Lin::constant(1)),
        Formula::or(vec![base.clone(), empty.clone()]),
    ];
    let mut e = Extending::new();
    for f in &cases {
        assert_eq!(e.answers(f), decided(f), "{f}");
        // Asked again, from what is remembered.
        assert_eq!(e.answers(f), decided(f), "{f} again");
    }
    // Each in a new memory, so that no answer depends on what was asked before.
    for f in &cases {
        assert_eq!(Extending::new().answers(f), decided(f), "{f} alone");
    }
}

#[test]
fn a_chain_of_extensions_is_decided_in_time_of_its_links() {
    // f{i} = f{i-1} && x + i * y <= 1000 i, over x >= y + 1: the conjunction of f{n} holds n
    // constraints, and deciding each f{i} whole costs O(n²) in all; each is decided from the
    // one it extends.
    let chain = |n: usize| {
        let mut f = Formula::and(vec![
            ge(sym("x"), sym("y").plus(&Lin::constant(1))),
            ge(sym("y"), Lin::constant(0)),
        ]);
        let mut out = Vec::with_capacity(n);
        for i in 1..=n as i64 {
            f = extend(&f, vec![sum(i, 1000 * i)]);
            out.push(f.clone());
        }
        out
    };
    let chains = zed_tests::scaling::inputs(200, chain);
    for f in chains[&200].iter().step_by(37) {
        assert_eq!(Extending::new().answers(f), decided(f), "{f}");
    }
    zed_tests::scaling::check("the answers of a chain of extensions", 200, |n| {
        let mut e = Extending::new();
        for f in &chains[&n] {
            let a = e.answers(f);
            assert_eq!((a.holds, a.fails), (Ok(true), Ok(true)));
        }
    });
}

#[test]
fn a_chain_whose_points_move_is_decided_whole() {
    // f{i} = f{i-1} && x + i * y >= 1000 i: the point found for f{i-1} is below the new
    // constraint, so each f{i} is decided whole, and each answer is still the one the whole has
    // (the Complexity tradeoff at `Extending::answers`).
    let mut f = Formula::and(vec![
        ge(sym("x"), sym("y").plus(&Lin::constant(1))),
        ge(sym("y"), Lin::constant(0)),
    ]);
    let mut e = Extending::new();
    for i in 1..=40i64 {
        f = extend(
            &f,
            vec![ge(
                sym("x").plus(&sym("y").times(i)),
                Lin::constant(1000 * i),
            )],
        );
        assert_eq!(e.answers(&f), decided(&f), "{f}");
    }
}
