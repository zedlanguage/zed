//! 03 edit distance, top-down memoized and bottom-up; a line with one word gives b = ""
//! (`w[1] else ""`); a line starting with a space gives a = "". Characters are code points.

fn step(a: &[char], b: &[char], up: usize, left: usize, diag: usize, i: usize, j: usize) -> usize {
    (up + 1)
        .min(left + 1)
        .min(diag + usize::from(a[i - 1] != b[j - 1]))
}

/// The memoized recurrence, on a stack of the cells waiting for their three neighbors.
fn top_down(a: &[char], b: &[char]) -> usize {
    let width = b.len() + 1;
    let mut memo: Vec<Option<usize>> = vec![None; (a.len() + 1) * width];
    let mut stack = vec![(a.len(), b.len())];
    while let Some(&(i, j)) = stack.last() {
        let cell = i * width + j;
        if memo[cell].is_some() {
            stack.pop();
        } else if i == 0 || j == 0 {
            memo[cell] = Some(i + j);
            stack.pop();
        } else if let (Some(up), Some(left), Some(diag)) =
            (memo[cell - width], memo[cell - 1], memo[cell - width - 1])
        {
            memo[cell] = Some(step(a, b, up, left, diag, i, j));
            stack.pop();
        } else {
            stack.extend([(i - 1, j), (i, j - 1), (i - 1, j - 1)]);
        }
    }
    memo[a.len() * width + b.len()].expect("the root was computed")
}

fn bottom_up(a: &[char], b: &[char]) -> usize {
    let mut d = vec![vec![0; b.len() + 1]; a.len() + 1];
    for i in 0..=a.len() {
        for j in 0..=b.len() {
            d[i][j] = if i == 0 || j == 0 {
                i + j
            } else {
                step(a, b, d[i - 1][j], d[i][j - 1], d[i - 1][j - 1], i, j)
            };
        }
    }
    d[a.len()][b.len()]
}

/// Runs the program.
pub fn run(lines: &[String], out: &mut String) -> Result<(), String> {
    for line in lines {
        let mut w = line.split(' ');
        let a = w.next().unwrap_or("");
        let b = w.next().unwrap_or("");
        let (ca, cb): (Vec<char>, Vec<char>) = (a.chars().collect(), b.chars().collect());
        say!(
            out,
            "{a} {b} {} {}",
            top_down(&ca, &cb),
            bottom_up(&ca, &cb)
        );
    }
    Ok(())
}
