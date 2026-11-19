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
//! woken. The facts are the names' intervals: star, starjoin, hubs, star_mixed, star_extra,
//! split4, rows_one_pair and stair_cover_free leave every name unbounded at every test, so for
//! these eight ([`PROBED`]) the relation is read too, after the last test (and after the join):
//! the facts after each probe of [`probes`], one name or two fixed to small values, which show
//! the relation's bounds on the other names there. A lost narrowing of the relation shows as a
//! wider interval after some probe. The probe lines were added at 3234d9327 (PERF-l139-under9,
//! l139c); the lines before them did not change.

use super::*;

/// The families whose tests leave every name unbounded, whose relation the probes read, each
/// with the largest size probed: split4, of five names and so 115 probes at each size, up to 6
/// (its probes up to 24 took 24 s at load 55; up to 6, 6.6 s), the others at every size.
const PROBED: [(&str, usize); 8] = [
    ("star", 24),
    ("starjoin", 24),
    ("hubs", 24),
    ("star_mixed", 24),
    ("star_extra", 24),
    ("split4", 6),
    ("rows_one_pair", 24),
    ("stair_cover_free", 24),
];

/// The probes of a scope of `names`: each name equal to each of -2 to 2, then each two names
/// equal to each pair of -1 to 1.
fn probes(names: &[Arc<str>]) -> Vec<(String, Term)> {
    let mut out = Vec::new();
    for n in names {
        for v in -2..=2 {
            out.push((format!("{n}={v}"), eq(var(n), int(v))));
        }
    }
    for (i, u) in names.iter().enumerate() {
        for w in &names[i + 1..] {
            for p in -1..=1 {
                for q in -1..=1 {
                    out.push((
                        format!("{u}={p},{w}={q}"),
                        and(eq(var(u), int(p)), eq(var(w), int(q))),
                    ));
                }
            }
        }
    }
    out
}

/// The lines of the probes of `s`, the scope of family `name` at size `k` after `at` (the
/// last test's number, or `join`).
fn probe_lines(out: &mut Vec<String>, name: &str, k: usize, at: &str, s: &Scope, f: &Family) {
    if !PROBED.iter().any(|&(n, most)| n == name && k <= most) {
        return;
    }
    let p = Premises::new();
    for (shown, t) in probes(&f.names) {
        let got = facts(&s.assume(&t, true, &p), &f.names);
        out.push(format!("{name} {k} {at} {shown} {got}"));
    }
}

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
        let last = f.tests.len().saturating_sub(1).to_string();
        probe_lines(&mut out, name, k, &last, &s, &f);
        if let Some(j) = &f.join {
            let joined = s.assume(j, true, &p).join(&s.assume(j, false, &p));
            out.push(format!("{name} {k} join {}", facts(&joined, &f.names)));
            probe_lines(&mut out, name, k, "join", &joined, &f);
        }
    }
    out
}

/// The probes at sizes 1 and 2 against the oracle: each probe on names of the family's window
/// (the oracle lists no other name, and takes a hub only in its one star), assumed after the
/// last test, gives the facts the oracle finds with the probe as one more test, and the scope
/// holds every point the oracle finds. All 460 such probes are exact at 3234d9327.
#[test]
fn probes_against_the_oracle() {
    let p = Premises::new();
    for (name, _) in PROBED {
        for k in 1..=2 {
            let f = family(name, k);
            let s = run(&f);
            let in_window = |n: &Arc<str>| f.window.iter().any(|w| *w.0 == **n);
            for (shown, t) in probes(&f.names) {
                if !f.names.iter().all(|n| !reads(&t, n) || in_window(n)) {
                    continue;
                }
                let probed = s.assume(&t, true, &p);
                let got = facts(&probed, &f.names);
                let mut tests = f.tests.clone();
                tests.push(t);
                let o = Oracle::of(&f.names, &tests, &f.window);
                let what = format!("{name} at k = {k}, probe {shown}");
                o.check_sound(&what, &probed, &got);
                assert_eq!(
                    got,
                    o.facts(&f.names),
                    "{what}: the scope's facts and the oracle's"
                );
            }
        }
    }
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
        "rows_one_pair", "wide_pairs", "wide", "drop_ends", "box_cases", "box_cases_y",
        "hole_end1_pad", "hole_end2_pad", "hub_eqs", "hub_alias", "unary_arms"
    ] &SIZES;
    split4_answers: ["split4"] &SIZES;
    one_size_answers: [
        "armlink", "armlink2", "armlink3", "coord3", "upper_release", "drop_end", "exit_order",
        "stair_hull", "stair_hull_vertices", "m1_trans_ce", "side1", "side2", "side3", "side4",
        "side5", "hole_end0", "hole_end1", "hole_end2", "hole1", "hole1s", "hole2", "hole2s",
        "hole2c"
    ] &[1];
    two_eq_case_answers: ["two_eq_case"] &[0, 1];
}
