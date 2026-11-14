//! The `llp` tool of plan row ZPARSE-par: the syntactic grammar read as a context-free grammar,
//! its LLP(1,1) pair table, and the conflicts left after each rule of the study. The tests run it
//! on the real grammar, on small grammars that show each kind of conflict and each rule, and at n
//! and 8n.

use zed_tools::llp::{self, Cfg, RULES, Report, read_rules, shared};
use zedc::parse::Grammar;

use super::{design, spec_dir, tool};

/// A small grammar over tokens with `Unit = Item* END`.
fn small(rules: &str) -> Grammar {
    let text = format!("Unit = Item* END  L1\n{rules}");
    Grammar::read_open(&[&text]).expect("a small grammar")
}

/// The report on `g` with the rules written in `text`.
fn report(g: &Grammar, text: &str) -> Report {
    let rules = read_rules(text).expect("rules");
    llp::check(g, "Unit", &rules).expect("the grammar reads")
}

#[test]
fn the_real_grammar_has_conflicts_and_the_two_virtual_tokens_remove_the_unbounded_ones() {
    let dir = spec_dir("llp_real", &design(""), "");
    let spec = zed_tools::spec::Spec::open(&dir.root()).expect("the real grammars");
    let g = &spec.syntactic;
    let base = report(g, "");
    assert!(
        base.unbounded_count > 0,
        "the annotation cycles: {:?}",
        base.cycles
    );
    assert!(
        base.cycles.iter().any(|c| c.contains("AnnotExpr")),
        "{:?}",
        base.cycles
    );
    assert!(base.head_only > 0, "{base:?}");
    assert!(
        base.dropped.contains("AnnotExpr: &AnnotEnd"),
        "{:?}",
        base.dropped
    );
    let after = report(g, RULES);
    assert_eq!(after.unbounded_count, 0, "{:?}", after.cycles);
    assert!(after.cycles.is_empty(), "{:?}", after.cycles);
    assert_eq!(after.head_only, 0);
    assert!(after.conflict_count < base.conflict_count);
    // The tool prints the same counts.
    let (outcome, out) = tool(llp::run, &[&dir.root()]);
    assert_eq!(outcome, Ok(true), "{out}");
    let first = format!(
        "pair conflicts {} ({} with no bound",
        base.conflict_count, base.unbounded_count
    );
    assert!(out.contains(&first), "{out}");
    assert!(out.contains("after head-close"), "{out}");
    assert!(
        out.contains(&format!("RESULT: {} pair conflicts", after.conflict_count)),
        "{out}"
    );
}

#[test]
fn two_stacks_for_one_pair_are_a_conflict_and_one_stack_is_not() {
    // After `x`, the token `n` starts `A` or `B`: the pair (`x`, `n`) has the stacks [A] and [B].
    let g = small("Item = 'x' A  L1\n  | 'x' B  L1\nA = 'n' ';'  L1\nB = 'n' ','  L1\n");
    let r = report(&g, "");
    assert_eq!(r.conflict_count, 1, "{:?}", r.stacks_of);
    assert_eq!(r.starts, 1);
    let stacks = &r.stacks_of["'x' 'n'"];
    assert_eq!(stacks.len(), 2);
    assert!(stacks.contains(&"[A]".to_string()) && stacks.contains(&"[B]".to_string()));
    // The pair is read at the item whose dot follows `x`, an item of `Item`.
    assert_eq!(r.conflicts["Item"], ["'x' 'n'"]);
    assert!(r.ll1["Item"] > 0);
    // One context for `n` after `x`: no conflict.
    let g = small("Item = 'x' A  L1\n  | 'y' B  L1\nA = 'n' ';'  L1\nB = 'n' ','  L1\n");
    let r = report(&g, "");
    assert_eq!(r.conflict_count, 0, "{:?}", r.stacks_of);
    assert!(r.pairs > 0 && r.ll1.is_empty(), "{r:?}");
}

#[test]
fn a_nullable_symbol_the_next_token_does_not_start_is_pushed() {
    // In `x n ;` and `x n + n ;` the pair (`n`, `;`) passes the empty `T`: the stack is
    // [T ';']. (With `T = ('+' 'n')?` the `n` in `T` is not followed by `T`, and the pair has
    // two stacks.)
    let g = small("Item = 'x' A ';'  L1\nA = 'n' T  L1\nT = ('+' 'n' T)?  L1\n");
    let r = report(&g, "");
    assert_eq!(r.conflict_count, 0, "{:?}", r.stacks_of);
    // Two items that end in `n` and pass a different number of empty symbols: two stacks.
    let g =
        small("Item = 'x' A ';'  L1\n  | 'y' A T ';'  L1\nA = 'n' T  L1\nT = ('+' 'n' T)?  L1\n");
    let r = report(&g, "");
    assert_eq!(r.conflict_count, 1, "{:?}", r.stacks_of);
    let stacks = &r.stacks_of["'n' ';'"];
    assert!(
        stacks
            .iter()
            .any(|s| s.ends_with("';']") && s.split(' ').count() == 3),
        "{stacks:?}"
    );
    let rest = r.conflict_count - r.unbounded_count - r.head_only - r.starts;
    assert_eq!(rest, 1);
}

/// An annotation that reaches to the end of an operator chain, as `AnnotExpr` does.
const ANNOT: &str = "Item = Or ';'  L1\nOr = Prefix ('|' Prefix)*  L1\n\
                     Prefix = Annot  L1\n  | 'n'  L1\nAnnot = '@' Or  L1\n";

#[test]
fn a_cycle_that_pushes_is_reported_and_a_virtual_closing_token_removes_it() {
    let g = small(ANNOT);
    let r = report(&g, "");
    assert!(r.unbounded_count > 0, "{r:?}");
    assert!(
        r.cycles
            .iter()
            .any(|c| c.contains("Annot") && c.contains("Or")),
        "{:?}",
        r.cycles
    );
    assert!(r.unbounded.contains_key("Or"), "{:?}", r.unbounded);
    let r = report(&g, "close: end of Annot -> CLOSE");
    assert_eq!(r.unbounded_count, 0, "{:?}", r.cycles);
    assert!(r.cycles.is_empty() && r.unbounded.is_empty());
    assert_eq!(r.conflict_count, 0, "{:?}", r.stacks_of);
}

#[test]
fn head_copies_give_conflicts_that_a_token_after_the_head_removes() {
    // `if n {}` reads `E` with the head flag set and `if n ;` without it.
    let rules =
        "Item = 'if' head(E) '{' '}'  L1\n  | 'if' E ';'  L1\nE = 'n'  L1\n  | !HEAD '{' '}'  L1\n";
    let g = small(rules);
    let r = report(&g, "");
    assert!(r.head_only > 0, "{:?}", r.stacks_of);
    let stacks = &r.stacks_of["'if' 'n'"];
    assert!(stacks.contains(&"[E@head]".to_string()), "{stacks:?}");
    let r = report(&g, "h: end of head -> HEAD_END");
    assert_eq!(r.head_only, 0, "{:?}", r.stacks_of);
    assert!(!r.stacks_of.contains_key("'if' 'n'"), "{:?}", r.stacks_of);
    let cfg = Cfg::of(
        &g,
        "Unit",
        &read_rules("h: end of head -> HEAD_END").expect("rules"),
    )
    .expect("reads");
    assert!(cfg.terms.contains(&"HEAD_END".to_string()));
    assert!(
        !cfg.nts.iter().any(|n| n.contains("@head")),
        "{:?}",
        cfg.nts
    );
}

#[test]
fn lookaheads_are_listed_and_left_recursion_is_rewritten() {
    let g = small("Item = 'x' !'y' L ';'  L1\nL = L '+' 'n'  L1\n  | 'n'  L1\n");
    let cfg = Cfg::of(&g, "Unit", &[]).expect("reads");
    assert!(cfg.dropped.contains("Item: !'y'"), "{:?}", cfg.dropped);
    assert!(cfg.nts.contains(&"L~".to_string()), "{:?}", cfg.nts);
    let r = report(&g, "");
    assert!(r.left.is_empty(), "{:?}", r.left);
    // Left recursion through another rule is listed, not rewritten.
    let g = small("Item = A ';'  L1\nA = B 'x'  L1\n  | 'n'  L1\nB = A 'y'  L1\n");
    let r = report(&g, "");
    assert_eq!(
        r.left,
        [vec!["A".to_string(), "B".to_string()]],
        "{:?}",
        r.left
    );
}

#[test]
fn a_re_tagging_rule_is_checked_against_the_token_before() {
    // A unary minus starts an item; a binary minus follows `n`.
    let rules = "Item = E ';'  L1\nE = Neg? 'n' ('-' 'n')*  L1\nNeg = '-'  L1\n";
    let g = small(rules);
    let r = report(&g, "neg: '-' in Neg -> NEG");
    assert!(shared(&r, "NEG", &["'-'"]).is_empty(), "{:?}", r.before);
    // A minus after `n` in both: the token before does not decide.
    let rules = "Item = E ';'  L1\nE = 'n' Neg? 'n'  L1\n  | 'n' '-' 'n' 'n'  L1\nNeg = '-'  L1\n";
    let g = small(rules);
    let r = report(&g, "neg: '-' in Neg -> NEG");
    assert_eq!(shared(&r, "NEG", &["'-'"]), ["'n'".to_string()].into());
}

#[test]
fn bad_rules_are_reported() {
    for (text, problem) in [
        ("neg '-' in Neg -> NEG", "rule line 1"),
        ("neg: '-' Neg -> NEG", "rule line 1"),
        ("neg: '-' in Neg", "rule line 1"),
        ("neg: '-' in -> NEG", "rule line 1"),
        ("# a comment\nneg: '-' in Neg ->", "rule line 2"),
        ("close: end Annot -> X", "rule line 1"),
    ] {
        match read_rules(text) {
            Err(e) => assert!(e.contains(problem), "{text}: {e}"),
            Ok(r) => panic!("{text}: read as {r:?}"),
        }
    }
    let g = small("Item = 'n' ';'  L1\nNeg = '-'  L1\n");
    for (text, problem) in [
        ("x: '-' in Missing -> X", "no rule Missing"),
        ("x: '+' in Item -> X", "re-tags no read of '+'"),
        ("x: end of Neg -> X", "ends no alternative"),
    ] {
        let rules = read_rules(text).expect("reads");
        match Cfg::of(&g, "Unit", &rules) {
            Err(e) => assert!(e.contains(problem), "{text}: {e}"),
            Ok(_) => panic!("{text}: no problem reported"),
        }
    }
    assert!(Cfg::of(&g, "Missing", &[]).is_err());
}

/// `n` rules that nest: `A0 = '(' A1 ')' T? | 'n'`, …, over a fixed set of terminals.
pub(super) fn nesting(n: usize) -> Grammar {
    let mut text = String::from("Item = A0 ';'  L1\nT = ('+' 'n' T)?  L1\n");
    for i in 0..n {
        let inner = if i + 1 < n {
            format!("A{}", i + 1)
        } else {
            "'n'".to_string()
        };
        text.push_str(&format!("A{i} = '(' {inner} ')' T  L1\n  | 'n' T  L1\n"));
    }
    small(&text)
}

/// The pair table of [`nesting`]`(n)` has more than `n` cores.
pub(super) fn pair_table_has_the_cores(g: &Grammar, n: usize) {
    let r = llp::check(g, "Unit", &[]).expect("reads");
    assert!(r.cores > n);
}

/// The checker reads [`nesting`] at small sizes; its time is held in `bench/llp.rs`.
#[test]
fn the_checker_reads_nested_rules_at_small_sizes() {
    for n in [1, 2, 9] {
        pair_table_has_the_cores(&nesting(n), n);
    }
}
