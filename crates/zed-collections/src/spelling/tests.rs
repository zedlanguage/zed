use super::{near_in_spelling, nearest};
use crate::seed::Rng;

/// The direct check: of the names visible at `at` and near `w`, the first in name order.
fn scan<'a>(names: &[(&'a str, std::ops::Range<usize>)], w: &str, at: usize) -> Option<&'a str> {
    (names.iter())
        .filter(|(n, r)| r.contains(&at) && near_in_spelling(w, n))
        .map(|(n, _)| *n)
        .min()
}

// The cases of DESIGN.md step L1.29e's test (each kind of slip, two near names, none near, a
// name declared after the site or in a scope that does not enclose it) are in
// tests/steps/l01_29_diagnostics/spelling_index.rs.

/// The written name's own spelling is not near it, and a second near name is still found.
#[test]
fn a_name_equal_to_the_written_one_is_passed_over() {
    let names = [("ab", 0..1), ("abc", 0..1)];
    assert_eq!(nearest(&names, &[("ab", 0)]), [Some("abc")]);
    assert_eq!(nearest(&names[..1], &[("ab", 0)]), [None]);
}

/// Visibility: a name is offered only inside its range, `from` included, `to` left out, and a
/// name declared twice where either range holds it.
#[test]
fn a_name_is_offered_only_where_it_is_visible() {
    let names = [("width", 3..7), ("width", 10..12)];
    let written: Vec<(&str, usize)> = (0..14).map(|at| ("widht", at)).collect();
    let got = nearest(&names, &written);
    for (at, g) in got.iter().enumerate() {
        let seen = (3..7).contains(&at) || (10..12).contains(&at);
        assert_eq!(g.is_some(), seen, "at {at}");
    }
}

/// A name one adjacent swap away (found by the swap lookup alone) is offered, and a rotation of
/// three characters, two slips away, is not.
#[test]
fn a_rotation_of_three_is_two_slips() {
    let names = [("abc", 0..1)];
    assert_eq!(nearest(&names, &[("bac", 0)]), [Some("abc")]);
    assert_eq!(nearest(&names, &[("bca", 0)]), [None]);
}

/// Seeded random batteries over a small alphabet, so that near names are common: the index
/// agrees with the direct check of each pair (`scan`) at every written name.
#[test]
fn the_index_agrees_with_a_check_of_each_pair() {
    let (mut rng, seed) = Rng::fresh("the_index_agrees_with_a_check_of_each_pair");
    let alphabet: Vec<char> = "abAB_".chars().collect();
    for round in 0..300 {
        let word = |rng: &mut Rng| -> String {
            let len = 1 + rng.below(5);
            (0..len).map(|_| rng.pick(&alphabet)).collect()
        };
        let places = 1 + rng.below(20);
        let owned: Vec<(String, std::ops::Range<usize>)> = (0..rng.below(12))
            .map(|_| {
                let a = rng.below(places + 1);
                let b = rng.below(places + 1);
                (word(&mut rng), a.min(b)..a.max(b))
            })
            .collect();
        let names: Vec<(&str, std::ops::Range<usize>)> =
            owned.iter().map(|(n, r)| (n.as_str(), r.clone())).collect();
        let owned_w: Vec<(String, usize)> = (0..1 + rng.below(12))
            .map(|_| (word(&mut rng), rng.below(places + 1)))
            .collect();
        let written: Vec<(&str, usize)> = owned_w.iter().map(|(w, a)| (w.as_str(), *a)).collect();
        let got = nearest(&names, &written);
        for (i, (w, at)) in written.iter().enumerate() {
            assert_eq!(
                got[i],
                scan(&names, w, *at),
                "seed {seed}, round {round}: `{w}` at {at} among {names:?}"
            );
        }
    }
}
