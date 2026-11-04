//! `cases SPEC_DIR`: bracketing tests. Each case of `zed/grammar/cases.txt` is parsed with a
//! start rule and printed as an s-expression. Each block of `zed/grammar/leftrec.txt` is a
//! grammar of its own and its cases.
//!
//! A case is `START[@RING] ::: TEXT ::: WANT`; WANT `ERROR` accepts any error. A case is one
//! line, so a line break in TEXT or WANT is written [`LINE_BREAK`].

use zedc::parse::{Grammar, Parser, TOP};

use crate::spec::Spec;
use crate::syntax::{Tokens, Tree, describe_fail, expected_strings, lex, then_end};
use crate::text::{read_text, strip};
use crate::{Outcome, arg, impl_root, say};

/// What a case writes for a line break.
pub const LINE_BREAK: char = '⏎';

/// One step of writing an s-expression.
enum Write<'a> {
    Text(&'a str),
    Node(usize),
}

/// The node `n` as an s-expression of its tokens: a node with one child spanning all of it is
/// that child.
pub fn sx(tree: &Tree, n: usize, toks: &Tokens) -> String {
    let text = |at: usize| toks.0[at].text.as_str();
    let mut out = String::new();
    let mut stack = vec![Write::Node(n)];
    while let Some(step) = stack.pop() {
        let n = match step {
            Write::Text(s) => {
                out.push_str(s);
                continue;
            }
            Write::Node(n) => n,
        };
        let node = tree.node(n);
        if !node.kids.is_empty() {
            if let [k] = node.kids[..]
                && tree.node(k).start == node.start
                && tree.node(k).end == node.end
            {
                stack.push(Write::Node(k));
                continue;
            }
            let mut parts = Vec::new();
            let mut pos = node.start;
            for &k in &node.kids {
                parts.extend((pos..tree.node(k).start).map(|i| Write::Text(text(i))));
                parts.push(Write::Node(k));
                pos = tree.node(k).end;
            }
            parts.extend((pos..node.end).map(|i| Write::Text(text(i))));
            out.push('(');
            stack.push(Write::Text(")"));
            for (i, part) in parts.into_iter().enumerate().rev() {
                stack.push(part);
                if i > 0 {
                    stack.push(Write::Text(" "));
                }
            }
            continue;
        }
        let words: Vec<&str> = (node.start..node.end).map(text).collect();
        out.push_str(&words.join(" "));
    }
    out
}

/// What the case `text` from `start` at `ring` gives.
fn show(lexical: &Grammar, syn: &Grammar, text: &str, start: &str, ring: u32) -> String {
    let toks = match lex(lexical, text) {
        Ok(toks) => toks,
        Err(e) => return format!("ERROR {e}"),
    };
    for t in &toks.0 {
        for h in &t.holes {
            let ht = match lex(lexical, h) {
                Ok(ht) => ht,
                Err(e) => return format!("ERROR in hole {e}"),
            };
            let mut q = Parser::new(syn, ring, &ht);
            if then_end(syn, &mut q, &ht, "Expr").is_none() {
                let expected = expected_strings(q.expected());
                return format!("ERROR in hole {}", describe_fail(q.far, &expected, &ht, 0));
            }
        }
    }
    let mut p = Parser::new(syn, ring, &toks);
    let Some((_, root)) = then_end(syn, &mut p, &toks, start) else {
        let expected = expected_strings(p.expected());
        return format!("ERROR@{} {}", p.far, expected.join(" "));
    };
    let tree = Tree {
        nodes: p.nodes,
        root,
    };
    sx(&tree, root, &toks)
}

/// Runs the cases `lines` over `syn` and says how many are wrong.
fn run_cases(
    lexical: &Grammar,
    syn: &Grammar,
    lines: &[&str],
    out: &mut String,
) -> Result<usize, String> {
    let mut bad = 0;
    for line in lines {
        let parts: Vec<&str> = line.split(" ::: ").map(strip).collect();
        let &[head, text, want] = &parts[..] else {
            return Err(format!("not START ::: TEXT ::: WANT: {line}"));
        };
        let (start, ring) = match head.split_once('@') {
            None | Some((_, "")) => (head.trim_end_matches('@'), TOP),
            Some((start, ring)) => (
                start,
                ring.parse().map_err(|_| format!("not a ring: {line}"))?,
            ),
        };
        let got = show(lexical, syn, &text.replace(LINE_BREAK, "\n"), start, ring);
        let got = got.replace('\n', &LINE_BREAK.to_string());
        let ok = got == want || (want == "ERROR" && got.starts_with("ERROR"));
        bad += usize::from(!ok);
        let tag = if ok { "ok   " } else { "DIFF " };
        say!(out, "{tag}{start} | {text}");
        say!(out, "       got  {got}");
        if !ok {
            say!(out, "       want {want}");
        }
    }
    Ok(bad)
}

/// Runs the tool.
pub fn run(args: &[String], out: &mut String) -> Outcome {
    let spec = Spec::open(arg(args, 0, "cases SPEC_DIR")?)?;
    let dir = format!("{}/zed/grammar", impl_root());
    run_files(&spec, &dir, out)
}

/// Runs the cases of `dir/cases.txt` and `dir/leftrec.txt`.
pub fn run_files(spec: &Spec, dir: &str, out: &mut String) -> Outcome {
    let text = read_text(&format!("{dir}/cases.txt"))?;
    let is_case = |l: &&str| !strip(l).is_empty() && !l.starts_with('#');
    let cases: Vec<&str> = text.split('\n').filter(is_case).collect();
    let bad = run_cases(&spec.lexical, &spec.syntactic, &cases, out)?;
    say!(out, "cases {} wrong {bad}", cases.len());

    let text = read_text(&format!("{dir}/leftrec.txt"))?;
    let mut blocks: Vec<(Vec<&str>, Vec<&str>)> = Vec::new();
    for l in text.split('\n').filter(is_case) {
        if l.starts_with("grammar ") {
            blocks.push((Vec::new(), Vec::new()));
            continue;
        }
        let Some(block) = blocks.last_mut() else {
            return Err(format!("leftrec.txt: a line before any grammar: {l}"));
        };
        if l.contains(" ::: ") {
            block.1.push(l);
        } else {
            block.0.push(l);
        }
    }
    let (mut n, mut bad_left) = (0, 0);
    for (grammar, lines) in &blocks {
        n += lines.len();
        let g = Grammar::read_open(&[&grammar.join("\n")])?;
        bad_left += run_cases(&spec.lexical, &g, lines, out)?;
    }
    say!(out, "left-recursion cases {n} wrong {bad_left}");
    Ok(bad + bad_left == 0)
}
