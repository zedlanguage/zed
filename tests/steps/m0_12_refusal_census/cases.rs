//! Completeness cases for the refusal census (TEST-complete-m0, author P189): how a diagnostic's
//! text is given its kinds, how a census line is written and counted, and how the programs file
//! is read and split, on inputs the census itself does not hold. The case list is
//! `COMPLETENESS.md`.

use super::{kinds, line, programs, report, totals};

#[test]
fn a_text_with_several_kinds_has_each_in_the_order_of_the_list() {
    let growth = kinds::KINDS[0].phrase;
    let tie = kinds::KINDS[3].phrase;
    let holes = kinds::KINDS[5].phrase;
    assert_eq!(
        kinds::of(&format!("{holes}\n{growth} / {tie}")),
        vec!["Growth", "Tie", "Holes"]
    );
    // A phrase written twice is one kind.
    assert_eq!(kinds::of(&format!("{tie}{tie}")), vec!["Tie"]);
}

#[test]
fn each_undecided_phrase_alone_is_of_kind_other_and_a_named_kind_wins() {
    for p in [
        "could not decide",
        "not proved wrong",
        "does not try",
        "Cannot find exactly",
        "could not work out",
        "Cannot expand",
    ] {
        assert_eq!(kinds::of(&format!("zedc {p} here")), vec!["Other"], "{p}");
    }
    // A kind's phrase and an undecided phrase: the kind only, never `Other` beside it.
    let pairs = kinds::KINDS[16].phrase;
    assert_eq!(
        kinds::of(&format!("zedc could not decide; {pairs}")),
        vec!["FunctionPairs"]
    );
    // No text, a phrase cut short, and a phrase in another case are no refusal.
    assert!(kinds::of("").is_empty());
    assert!(kinds::of("could not decid").is_empty());
    assert!(kinds::of("COULD NOT DECIDE").is_empty());
}

#[test]
fn every_kind_has_a_distinct_name_and_a_phrase_no_other_kind_holds() {
    let ks = kinds::KINDS;
    for (i, a) in ks.iter().enumerate() {
        assert!(!a.phrase.is_empty(), "{}", a.name);
        assert_ne!(a.name, "Other");
        for b in &ks[i + 1..] {
            assert_ne!(a.name, b.name);
            assert!(
                !a.phrase.contains(b.phrase) && !b.phrase.contains(a.phrase),
                "{} and {}",
                a.name,
                b.name
            );
        }
        // Each phrase marks its own kind alone.
        assert_eq!(kinds::of(a.phrase), vec![a.name]);
    }
}

#[test]
fn a_census_line_is_tab_separated_on_one_line() {
    let mut out = String::new();
    line(
        &mut out,
        "unit.zed",
        "3:7",
        "warning",
        &["Growth", "Tie"],
        "  first\nsecond\n",
    );
    line(&mut out, "u", "load", "rejected", &["Other"], "why");
    assert_eq!(
        out,
        "unit.zed\t3:7\twarning\tGrowth,Tie\tfirst / second\nu\tload\trejected\tOther\twhy\n"
    );
}

#[test]
fn totals_count_each_kind_of_each_line_in_the_list_order_and_leave_out_zeros() {
    let out = "a\t1:1\trejected\tTie,Growth\tx\n\
               b\t2:1\twarning\tGrowth\ty\n\
               c\tload\trejected\tOther\tz\n";
    assert_eq!(totals(out), "Growth: 2\nTie: 1\nOther: 1\n");
    // A kind named inside the reason is not counted; only the fourth field is.
    assert_eq!(totals("a\t1:1\twarning\tTie\tGrowth\n"), "Tie: 1\n");
    // A name that only begins like a kind is not that kind.
    assert_eq!(totals("a\t1:1\twarning\tTies\tx\n"), "");
    // No line: no totals, and the report is the empty census after a blank line.
    assert_eq!(totals(""), "");
    assert_eq!(report(""), "\n");
    assert_eq!(report(out), format!("{}\n{out}", totals(out)));
}

#[test]
fn the_programs_file_reads_back_to_its_bytes() {
    let path = zed_tests::steps_dir().join("m0_12_refusal_census/programs.txt");
    let bytes = std::fs::read(&path).expect("programs.txt");
    let units = programs::read(&path);
    assert_eq!(units.len(), 120);
    let mut again = Vec::new();
    for (origin, text) in &units {
        let (_, hash) = origin.rsplit_once('#').expect("an origin ends in #<hash>");
        assert!(
            hash.len() == 8 && hash.bytes().all(|b| b.is_ascii_hexdigit()),
            "{origin}"
        );
        again.extend(format!("== {origin} {}\n{text}\n", text.len()).bytes());
    }
    assert_eq!(again, bytes);
    assert_eq!(programs::all(), &units[..]);
}

#[test]
fn the_pieces_of_the_programs_cover_every_unit_once_in_order() {
    let all = programs::all();
    for n in [1, 7, 12, 120] {
        let joined: Vec<_> = (0..n).flat_map(|k| programs::piece(k, n)).collect();
        assert_eq!(joined, all.iter().collect::<Vec<_>>(), "{n} pieces");
        let sizes: Vec<usize> = (0..n).map(|k| programs::piece(k, n).len()).collect();
        let (lo, hi) = (sizes.iter().min().unwrap(), sizes.iter().max().unwrap());
        assert!(hi - lo <= 1, "{n} pieces: {sizes:?}");
    }
    // More pieces than units: some pieces are empty, and still every unit is in one.
    let n = 121;
    assert_eq!(
        (0..n).map(|k| programs::piece(k, n).len()).sum::<usize>(),
        120
    );
    assert!((0..n).any(|k| programs::piece(k, n).is_empty()));
}
