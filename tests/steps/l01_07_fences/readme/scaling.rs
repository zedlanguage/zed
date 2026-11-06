//! The time to read a page's stated results and compare them with the table of expected results
//! is linear in the number of fences.

use zed_tests::fences::DocFence;
use zed_tests::readme::{self, Entry};
use zed_tests::scaling::check;

/// A page of `n` sections, each with a fence, a trailing comment, a text block and a captioned
/// table with a cell spanning two rows; its fences; and its table of expected results.
fn inputs(n: usize) -> (String, Vec<DocFence>, Vec<Entry>) {
    let mut page = String::new();
    let mut fences = Vec::with_capacity(n);
    for i in 0..n {
        page.push_str(&format!(
            "### Section {i}\n\n```zed\nx{i} = 1;   // 1\n```\n\n```text\nx{i} = 1\n```\n\n\
             **`x{i}`**\n\n<table>\n<tr><th>k</th><th>v</th></tr>\n\
             <tr><td rowspan=\"2\"><code>a</code></td><td>1</td></tr>\n<tr><td>2</td></tr>\n\
             </table>\n\n"
        ));
        fences.push(DocFence {
            key: format!("README.md [Section {i}] 1"),
            at: format!("README.md:{}", 3 + 18 * i),
            layer: 1,
            ring: 1,
            notation: false,
            text: format!("x{i} = 1;   // 1"),
        });
    }
    let keys: Vec<String> = fences.iter().map(|f| f.key.clone()).collect();
    let table = readme::entries(&readme::render(&keys, &readme::stated(&page)))
        .expect("the rendered table reads back");
    (page, fences, table)
}

#[test]
fn reading_and_comparing_stated_results_is_linear() {
    let n = 4_000;
    let small = inputs(n);
    let large = inputs(8 * n);
    assert!(super::problems(&small.0, &small.1, &small.2).is_empty());
    check("README stated results, by fences", n, |size| {
        let (page, fences, table) = if size == n { &small } else { &large };
        assert!(super::problems(page, fences, table).is_empty());
    });
}
