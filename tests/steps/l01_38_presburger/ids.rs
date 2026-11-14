//! The keys by which the store knows a part of a formula that more than one parent holds
//! (ADDR-presburger): the id a part is given when it is made, never its address (SYNTHESIS
//! fact 2). The answers do not depend on where the parts are in memory, a key costs no room in
//! the formula, and a pass reads each shared part once, so its cost follows the distinct parts.

use std::mem::size_of;

use zedc::store::conjuncts::Conjuncts;
use zedc::store::presburger::{Atom, Con, Formula, Lin, Shared, project_each};

pub(super) fn atom(n: &str) -> Atom {
    Atom::Sym(n.into())
}

/// `a x + b y + c >= 0`.
fn ge(a: i64, b: i64, c: i64) -> Formula {
    let l = (Lin::atom(atom("x")).times(a))
        .plus(&Lin::atom(atom("y")).times(b))
        .plus(&Lin::constant(c));
    Formula::Con(Con::ge(&l, &Lin::constant(0)))
}

/// The chain of rules `a0 = x >= 0 && y >= 0` and `ai = (x <= i && y >= -i) <join> a(i-1)
/// <join> a(i-2)`, each a name kept whole where it is used ([`Formula::and_keeping`],
/// [`Formula::or_keeping`]), so each rule is one part held by the two after it, and the chain
/// written out holds `a0` a number of times exponential in `d`. `pad` runs before each rule is
/// made, to move where it lands in memory. Returns `ad` and the rules.
pub(super) fn chain(d: usize, and: bool, pad: &mut dyn FnMut()) -> (Formula, Vec<Formula>) {
    pad();
    let mut rules = vec![Formula::and(vec![ge(1, 0, 0), ge(0, 1, 0)])];
    for i in 1..=d as i64 {
        let mut fs = vec![Formula::and(vec![ge(-1, 0, i), ge(0, 1, i)])];
        fs.extend(rules.iter().rev().take(2).cloned());
        pad();
        rules.push(if and {
            Formula::and_keeping(fs, |j| j > 0)
        } else {
            Formula::or_keeping(fs, |j| j > 0)
        });
    }
    (rules.last().expect("the last rule").clone(), rules)
}

/// The permutation that sorts the rules by the address of their parts.
fn address_order(rules: &[Formula]) -> Vec<usize> {
    let at = |f: &Formula| match f {
        Formula::And(gs) | Formula::Or(gs) => &**gs as *const Vec<Formula> as usize,
        Formula::Con(_) | Formula::Not(_) => unreachable!("a rule is a conjunction or disjunction"),
    };
    let mut order: Vec<usize> = (0..rules.len()).collect();
    order.sort_by_key(|&i| at(&rules[i]));
    order
}

/// What the passes keyed by a shared part give for the chains `and` and `or`: the conjuncts
/// added one by one (`Conjuncts::and`), the atoms and constraints (folds), the projections onto
/// `x` and `y` (each shared disjunct projected once per base, `project_parts`), the order of
/// the chain against itself extended, and the chains shown.
fn answers(and: &Formula, or: &Formula) -> Vec<String> {
    let mut c = Conjuncts::default();
    c.and(and.clone());
    let syms = [atom("x"), atom("y")];
    let longer = Formula::and_keeping(vec![and.clone(), ge(1, 0, 1)], |j| j == 0);
    vec![
        format!("{:?}", c.set()),
        format!("{:?} {:?}", and.atoms(), or.atoms()),
        format!("{:?} {:?}", and.cons(), or.cons()),
        format!("{:?}", project_each(and, &syms)),
        format!("{:?}", project_each(or, &syms)),
        format!("{:?}", and.cmp(&longer)),
        and.to_string(),
        or.to_string(),
    ]
}

#[test]
fn a_key_costs_no_room_in_the_formula() {
    // The id is kept with the parts, behind the one pointer a node held before.
    assert_eq!(size_of::<Shared<Vec<Formula>>>(), size_of::<usize>());
    assert_eq!(size_of::<Shared<Formula>>(), size_of::<usize>());
    assert_eq!(size_of::<Option<Shared<Formula>>>(), size_of::<usize>());
}

#[test]
fn three_allocation_orders_read_alike() {
    // The passes know a shared part by its key while they run; the answers must not depend on
    // where the parts are in memory.
    let d = 12;
    let build = |pad: &mut dyn FnMut()| {
        let (and, ands) = chain(d, true, pad);
        let (or, ors) = chain(d, false, pad);
        (and, or, ands.into_iter().chain(ors).collect::<Vec<_>>())
    };
    // In order, with nothing between the parts.
    let (and0, or0, rules0) = build(&mut || {});
    // With blocks of growing size held between the parts, so each part lands further on.
    let mut held: Vec<Vec<u8>> = Vec::new();
    let (and1, or1, rules1) = build(&mut || held.push(vec![7; 24 + held.len()]));
    // Into holes: parts of the size of a rule's are made and freed, every other one, last
    // first, before each rule, so the allocator hands back freed blocks in an order of its own.
    let mut holes = || {
        let blocks: Vec<Shared<Vec<Formula>>> = (0..9).map(|_| Shared::new(Vec::new())).collect();
        blocks.into_iter().rev().step_by(2).for_each(drop);
    };
    let (and2, or2, rules2) = build(&mut holes);
    let orders = [
        address_order(&rules0),
        address_order(&rules1),
        address_order(&rules2),
    ];
    assert!(
        orders[0] != orders[1] || orders[0] != orders[2] || orders[1] != orders[2],
        "the three builds put the parts in the same order in memory, so the test reads one order"
    );
    let first = answers(&and0, &or0);
    assert_eq!(answers(&and1, &or1), first);
    assert_eq!(answers(&and2, &or2), first);
    // The conjunction holds where `a0` does with `x <= 1`.
    assert_eq!(
        first[3],
        "Ok(([Ok(IntervalSet { pieces: [(Fin(Num(Small(0))), Fin(Num(Small(1))))] }), \
         Ok(IntervalSet { pieces: [(Fin(Num(Small(0))), PosInf)] })], []))"
    );
    drop(held);
}
