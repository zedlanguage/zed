//! The answers of the families at each size up to 24, pinned: the facts after each test that
//! changes them, and after the join (`answers.txt`, one line each, `family k test facts` with
//! the tests counted from 0). The work done to keep these families under the limit of growth
//! (PERF-l139-under9) skips projections whose result it proves unchanged, such as the parts of
//! a chain above its least part (`Block::update` in `zedc-preimage`'s `product.rs`); a skip
//! that loses a narrowing of a name changes a line here. The oracle of `families.rs` lists
//! points only at small sizes; these sizes go up to 24.
//!
//! `answers.txt` was written at 65bf4b76c, and the same lines came from 65bf4b76c with the
//! lazy wake of a recession bucket (66eca8290) turned off, so from every part of each chain
//! woken. The facts are the names' intervals only: star, starjoin, hubs, star_mixed,
//! star_extra, split4, rows_one_pair and stair_cover_free leave every name unbounded at every
//! test, so a lost narrowing of their relation that no interval shows is not caught here.

use super::*;

/// The sizes at which a family that takes one is run.
const SIZES: [usize; 10] = [1, 2, 3, 4, 5, 6, 8, 12, 16, 24];

const ANSWERS: &str = include_str!("answers.txt");

/// The lines of `name` at each of `sizes`: the facts after each test that changes them, then
/// at the join.
fn answers(name: &str, sizes: &[usize]) -> Vec<String> {
    let p = Premises::new();
    let mut out = Vec::new();
    for &k in sizes {
        let f = family(name, k);
        let mut s = ints(&f.names);
        let mut last = String::new();
        for (i, t) in f.tests.iter().enumerate() {
            s = s.assume(t, true, &p);
            let got = facts(&s, &f.names);
            if got != last {
                out.push(format!("{name} {k} {i} {got}"));
                last = got;
            }
        }
        if let Some(j) = &f.join {
            let joined = s.assume(j, true, &p).join(&s.assume(j, false, &p));
            out.push(format!("{name} {k} join {}", facts(&joined, &f.names)));
        }
    }
    out
}

fn check_answers(names: &[&str], sizes: &[usize]) {
    for name in names {
        let got = answers(name, sizes);
        let want: Vec<&str> = (ANSWERS.lines())
            .filter(|l| l.split(' ').next() == Some(name))
            .collect();
        for (g, w) in got.iter().zip(&want) {
            assert_eq!(g, w, "{name}");
        }
        assert_eq!(got.len(), want.len(), "{name}: the number of lines");
    }
}

/// One test for each group of families, each under the time limit of a test.
macro_rules! pinned {
    ($($test:ident: [$($name:literal),*] $sizes:expr;)*) => {
        $(
            #[test]
            fn $test() {
                check_answers(&[$($name),*], $sizes);
            }
        )*
    };
}

pinned! {
    star_answers: ["star", "starjoin", "hubs"] &SIZES;
    star_extra_answers: ["star_extra"] &SIZES;
    star_mixed_answers: ["star_mixed"] &SIZES;
    chain_answers: ["chain"] &SIZES;
    boxstar_answers: ["boxstar", "cuts"] &SIZES;
    persist_answers: ["persist"] &SIZES;
    coordkk_answers: ["coordkk", "coordkk_y"] &SIZES;
    coordmix_answers: ["coordmix", "coordmix_shift", "coordmix_floor"] &SIZES;
    coordmix_unmatched_answers: ["coordmix_unmatched", "coordmix_slopes"] &SIZES;
    stair_answers: [
        "stair_holes", "stair_holes_mix", "stair_holes_late", "stair_cover", "stair_cover_free"
    ] &SIZES;
    hop_answers: ["hop", "hopon"] &SIZES;
    hopb_answers: ["hopb", "hoponb"] &SIZES;
    sized_answers: [
        "rows_one_pair", "wide_pairs", "wide", "drop_ends", "box_cases", "box_cases_y", "split4",
        "hole_end1_pad", "hole_end2_pad", "hub_eqs", "hub_alias", "unary_arms"
    ] &SIZES;
    one_size_answers: [
        "armlink", "armlink2", "armlink3", "coord3", "upper_release", "drop_end", "exit_order",
        "stair_hull", "stair_hull_vertices", "m1_trans_ce", "side1", "side2", "side3", "side4",
        "side5", "hole_end0", "hole_end1", "hole_end2", "hole1", "hole1s", "hole2", "hole2s",
        "hole2c"
    ] &[1];
    two_eq_case_answers: ["two_eq_case"] &[0, 1];
}
