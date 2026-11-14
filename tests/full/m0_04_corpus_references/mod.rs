//! Reference 14 against its O(n²) form on every sequence of 5 points of the 3 by 3 grid: 472,392
//! inputs, about 7 s, too long for the local suite, whose test
//! `m0_04_corpus_references::clustering_agrees_with_its_quadratic_form_on_every_small_grid_input`
//! takes the sequences of up to 4 points. It needs no tool outside the Rust toolchain.

#[path = "../../steps/m0_04_corpus_references/p14_oracle.rs"]
mod p14_oracle;

/// The lines of `text`, as reference 14 reads a file of it.
fn input_lines(text: &str) -> Vec<String> {
    let body = text.strip_suffix('\n').unwrap_or(text);
    body.split('\n').map(String::from).collect()
}

/// Every sequence of 5 points of the 3 by 3 grid, points repeated or not, with every count of
/// clusters from -1 to 6. Every order of every set is here, so this also checks that reordering
/// the input lines renames the clusters as the O(n²) form does.
#[test]
fn clustering_agrees_with_its_quadratic_form_on_every_grid_input_of_five_points() {
    let grid: Vec<String> = (0..9).map(|c| format!("{} {}\n", c % 3, c / 3)).collect();
    let mut points = vec![String::new()];
    for _ in 0..5 {
        points = points
            .iter()
            .flat_map(|body| grid.iter().map(move |p| format!("{body}{p}")))
            .collect();
    }
    let run = zed_corpus_ref::program("14").expect("reference 14");
    let (mut seen, mut differ, mut first) = (0, 0, None);
    for body in &points {
        for k in -1..=6 {
            let text = format!("{k}\n{body}");
            let lines = input_lines(&text);
            let (mut got, mut want) = (String::new(), String::new());
            let got_result = run(&lines, &mut got);
            let want_result = p14_oracle::run(&lines, &mut want);
            seen += 1;
            if (got, got_result) != (want, want_result) {
                differ += 1;
                first.get_or_insert(text);
            }
        }
    }
    assert_eq!(seen, 472_392);
    assert_eq!((differ, first), (0, None), "of {seen} inputs");
}
