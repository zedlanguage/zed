# ZPARSE-par: parallel parsing of sec:grammar

Study by agent ZPARSE-par, 2026-11-12, at commit 358024323, spec commit 69e8c8e. Tools: `crates/zed-tools/src/split.rs` (`split SPEC_DIR [FILE…]`) and `crates/zed-tools/src/llp.rs` (`llp SPEC_DIR [RULES]`). Tests: `tests/steps/m0_03_grammar_tools/split.rs` and `llp.rs`. No grammar change: the DESIGN text below is proposed, not applied.

Key to plan IDs:

| Plan ID | What it covers |
|---|---|
| ZPARSE-par | this study |
| LANIUS-study | the study of the laniusc GPU compiler that proposed this row |
| GPU-front | the self-hosted front end on `#gpu`, which uses the parse this study specifies |
| ZLEX-scan | Zed's own lexer as a parallel scan |
| PAR-tree-ops | `matchBrackets` and the prefix-maximum tree in libzed |
| S.2, S.3 | the lexer and the parser written in Zed |

Terms. An *item* is one match of the rule `Item` in `Unit = Item* END`: a top-level declaration, binding, statement or test. *Depth* is the number of open `(`, `[` and `{` before a token. LLP(1,1) is the parallel LL parsing of Vagner and Melichar (2007), the method laniusc uses: each pair of adjacent tokens is looked up in a table that gives the piece of the left-most derivation between them, so all pairs are handled at once.

## Summary

- **Part (a) holds.** One depth scan finds the item boundaries, and parsing each segment alone gives the whole-file parse, node for node. On the 287 programs of the corpus (DESIGN.md and EXAMPLES.md fences and every `.zed` file of this repository), the 285 that lex give the same parse both ways, including the 18 that do not parse; the scan cuts 825 of the 833 item boundaries.
- **The 8 boundaries the scan does not cut** follow a `}`: 7 before `@foreign` (an annotation can follow a block inside an item) and 1 before an item named `tree` (a ReducePolicy word can follow a reduction block). The segment then holds two items; the parse is still the same.
- **Part (b): the grammar has no LLP(1,1) form.** With no re-tagging, the pair table has 1860 conflicts, 475 of them with stacks of no bound. Two virtual tokens, one at the end of each annotation and one at the end of each `if`, `match`, `for` and `where` head, remove every stack with no bound and every conflict from the head copies of rules, and leave 1320. The three token re-taggings tried (unary minus, call parenthesis, block brace) each add conflicts, since the token before does not decide them.
- **16 PEG lookaheads have no LLP form**, listed below. Left recursion through other rules: none.
- **What is left** comes from one token starting an expression, a type and a pattern at once, from operand levels that differ between operators, and from optional words after a reduction. Removing it needs a cover grammar for expressions, types and patterns and uniform operand levels: a redesign of sec:grammar, proposed below for the author when GPU-front comes near.
- **Decision.** GPU-front uses the split of part (a): a depth scan, then the PEG parse of each segment. It needs no grammar change. The LLP route is recorded, not taken.

## Part (a): one depth scan, then a PEG parse per item

### The scan

The scan reads the token kinds and keeps the depth. A position between tokens `a` and `b`, both at depth 0, is a cut when no string of `Item` holds a token like `a` followed by a token like `b` at depth 0. The set of such pairs is computed once from the grammar (`Splitter::new`), with the grammar read without order or lookahead: ordered choice is choice, and `&e` or `!e` is a branch that reads `e` and stops. That reading only adds strings, so a pair it lacks is in no item, and every cut is an item boundary of the whole-file parse.

The real grammar gives 1950 pairs over 93 terminals. Brackets balance in every match of `Item`, which `Splitter::new` checks: it reports a match that leaves a bracket open, closes one it did not open, closes with the wrong kind, repeats an unbalanced part, or matches no tokens.

### Why each segment parses as in the whole file

A segment is parsed over its own tokens with no `END` after it, so every test at its end fails. In the whole file every test at a cut fails too: a test that read the token after the cut would put that pair at depth 0 into a string of `Item`, which the cut excludes, and a test for `END` fails because the file goes on. So each item reads the same results in both parses. When the file has no parse, the failure is the one of the first segment that fails, merged with the farthest failures of the segments before it (`split_parse`).

### Results on the corpus

| Measure | Count |
|---|--:|
| programs | 287 |
| lex errors (two variant fences under `zed/fences/variants/`) | 2 |
| parse errors, same failure both ways | 18 |
| programs with unbalanced brackets | 0 |
| tokens in the programs that parse | 36,593 |
| items | 1,100 |
| item boundaries | 833 |
| boundaries cut | 825 |
| boundaries not cut: `}` then `@foreign` (first at DESIGN.md, the struct `Sample` before `@foreign("sensor", …)`) | 7 |
| boundaries not cut: `}` then the item `tree = xs …` (EXAMPLES.md, the `tree` ReducePolicy) | 1 |
| programs whose split parse differs from the whole-file parse | 0 |

Damaged copies (a token removed at n/4, n/2 and 3n/4, a token doubled at n/3) of every corpus `.zed` file also give the same parse both ways (`split_parse_equals_whole_file_parse_on_damaged_programs`). A control that cuts at every depth-0 position, ignoring the pairs, gives a different parse on more than 30 programs, so the comparison does catch a cut inside an item.

### Proposed DESIGN text (sec:grammar, new paragraph "Parsing items in parallel")

> A parser may split a unit into segments before parsing it. Two adjacent tokens at bracket depth 0 that no string of `Item` holds next to each other at depth 0 always lie in different items, so the position between them is an item boundary. One scan over the tokens, keeping the bracket depth, finds all such positions; each segment is then parsed as `Item*` alone. The items, their trees and the first syntax error are the same as those of the whole unit. A unit whose brackets do not balance is parsed whole.

The two kinds of boundary the scan misses need no text: they only make a segment hold two items. A grammar change that removed them (an annotation only before a declaration; ReducePolicy words reserved) is not proposed: 8 of 833 boundaries is not worth a language change.

## Part (b): the LLP(1,1) checker

### Method

`llp` reads sec:grammar as a context-free grammar (`Cfg::of`):

- ordered choice becomes choice;
- `X*`, `X+`, `X?` and groups become helper nonterminals;
- `head(…)` and `!HEAD` become copies of the rules reached inside a head, marked `@head`;
- direct left recursion (`A = A x | y`) becomes a right-recursive tail `A~`, and left recursion through other rules is reported;
- each lookahead `&e` and `!e` is read as the empty string and listed.

A re-tagging rule (`RULES` in llp.rs, or a file) has one of two forms:

- `NAME: TOKEN in RULE… -> NEW` reads TOKEN as NEW wherever one of the RULEs reads it;
- `NAME: end of RULE… -> NEW` appends NEW to every alternative of each RULE (`end of head` appends it to every `head(…)`), a virtual token that a scan would place.

The pair table is built from items (production, dot, terminal after the dot) and stacks. Each pair (x, y) of adjacent tokens is reached by stepping back over the symbol before the dot of the item at y:

- a terminal x gives the pair with stack [x];
- entering a nonterminal B from its first symbol keeps the stack;
- stepping over B when y starts B gives stack [B];
- stepping over a nullable B when y does not start B pushes B.

A pair is a conflict when it has two stacks or more, so the token pair alone does not say which piece of the derivation lies between the tokens. A cycle of steps that pushes gives stacks with no bound; Tarjan's components find these cycles, and every core they reach gets one stack, marked "no bound", so the work ends. laniusc instead builds the item sets of Vagner and Melichar; on this grammar that construction passed 1,700 sets with 660 queued after 40 s and did not end, since the annotation cycles below make the sets unbounded.

### The grammar as read

| Measure | Count |
|---|--:|
| PEG rules | 175 |
| nonterminals after the reading | 551 |
| productions | 1,098 |
| terminals | 93 |
| lookaheads read as the empty string | 16 |
| left recursion through other rules | 0 |
| cycles that push with no bound, by rule | 8: Additive, And, AscChain, DescChain, EqChain, Multiplicative, Or, Reduce |

Every pushing cycle passes through `Prefix > AnnotExpr > Or`: an annotation reaches to the end of the operator chain inside it, so after `@a x + y`, the next token may close any number of nested annotated operands.

### PEG constructs with no LLP form

These 16 lookaheads are read as the empty string. Each decides a choice by tokens that the LLP pair table cannot see:

| Rule | Lookahead |
|---|---|
| AnnotExpr | `!'-'` |
| AnnotExpr | `&AnnotEnd` |
| Annotated | `&ANNOT` |
| Arm | `!'{'` |
| ElseTail | `!'{'` |
| GPrimary | `!'sep'` |
| Item | `!(Annot ';')` |
| KeyTerm | `!('(' nest(JoinExpr) ')' !KeyOp)` |
| KeyTerm | `!KeyOp` |
| Lambda | `!'{'` |
| Level | `&')'` |
| PlainArg | `!(Name ':')` |
| Primary | `&('{' Item)` |
| SortArg | `&(',' \| ')')` |
| TypeUnion | `!'\'` |
| TypeUnion | `!('\|' \| '&')` |

Ordered choice itself has no LLP form either: where two alternatives match the same tokens, the PEG takes the first and the CFG reading has both, which shows as an LL(1) conflict.

### Conflicts, and what each rule removes

Conflicts by kind: "no bound" is a pair one of whose stacks has no bound; "HEAD copies" is a pair whose stacks are equal once `@head` is removed; "starts" is a pair whose stacks are each one symbol, so the second token starts a construct the pair does not name; "tails" is the rest, where the chains of rules that end between the two tokens differ.

| After | LL(1) conflicts | Pair conflicts | Change | No bound | HEAD copies | Starts | Tails | The token before decides? |
|---|--:|--:|--:|--:|--:|--:|--:|---|
| no re-tagging | 430 | 1,860 | | 475 | 394 | 518 | 473 | |
| `annot-close: end of AnnotExpr -> ANNOT_END` | 393 | 1,841 | −19 | 0 | 491 | 518 | 832 | a virtual token |
| then `head-close: end of head -> HEAD_END` | 270 | 1,320 | −521 | 0 | 0 | 494 | 826 | a virtual token |

Without re-tagging the table has 33,575 cores, 70,647 items, 2,015 stacks and 2,248 pairs. A run takes about 0.7 s and 53 MB in the debug build.

`annot-close` removes few conflicts by count, but it removes all 475 with no bound: those pairs are now conflicts between bounded stacks, which is why the "tails" count grows. Without it no parser of this kind can be built at all.

Three token re-taggings were measured after `annot-close`; each adds conflicts, because splitting a token's tag only helps when the token before tells the two tags apart, and here it does not:

| Rule | Pair conflicts | Change | Both tags follow |
|---|--:|--:|---|
| `neg: '-' in Prefix SignedLit -> NEG` | 1,864 | +23 | `(` `)` `?` `}` IDENT |
| `call-open: '(' in CallSuffix FacetCall TypeApply AtomApply CtorPat AtomPattern Function Method Law AnnotExpr -> CALL_OPEN` | 1,895 | +31 | `)` `?` `}` ANNOT IDENT STRING |
| `block-open: '{' in Block -> BLOCK_OPEN` | 1,938 | +43 | 65 tokens, nearly every token |

The rule file for this table is the four lines `annot-close: end of AnnotExpr -> ANNOT_END`, then the three rules above, passed as `llp SPEC_DIR FILE`.

### What the 1,320 conflicts left come from

The rules with the most pair conflicts left are Literal (225), SignedLit (160), Display (135), ReduceTail (100), Refinement (100), Block (97) and AnnotExpr (90); the tool prints the whole list with examples. They fall into five causes:

1. **One token starts an expression, a type and a pattern.** After `,` the token `-` starts a stack of [Expr], [Expr12], [Entry], [Type], [SignedLit], [TupleType.178], [ShapeDim], [Arm], [Pattern], [TypeParam], [Args.157], [Refinement] or [TestCase]. The pair `( -` is the same. A PEG decides by the rule it is in; the pair table sees only two tokens.
2. **`{` opens a block, a record display, a match body, a test table or a struct body.** `{ -` has the stacks [Entry], [Block.73], [SignedLit], [Arm] and [TestCase].
3. **`-` is binary minus, unary minus, or the sign of a literal.** `- INT` has [Multiplicative], [Prefix] and [SignedLit.110].
4. **Operand levels differ between operators.** ReduceTail takes a Postfix operand, RangeTail an Additive one, and Type contains Expr, so after `INT` before `;` the chain of rules that ends there is one of several: [Postfix~ Multiplicative~ Additive~ Reduce~ And~ Or~ Expr12~ ';'], a chain through ReduceTail, or a chain through a type.
5. **Optional words after a construct.** `compensated ;` ends a ReducePolicy word or an identifier-like operand.

Statement positions add a sixth, smaller group: `; -` has [Unit.2], [Block.73] and [ShapeDim].

### Proposed DESIGN text, for the author when GPU-front is planned

This is a redesign of sec:grammar, measured only in part (the two virtual tokens); it is not proposed for now.

1. **Virtual tokens a scan places.** After bracket matching (PAR-tree-ops `matchBrackets`), two scans place two tokens the lexer does not write:
   - `HEAD_END`: the heads of `if`, `match`, `for`, the generator `in` and `where` are openers; the first `{` at the head's depth not preceded by `with` closes the innermost open head, and `HEAD_END` goes before it. This is bracket matching plus one token of look-back.
   - `ANNOT_END`: each annotation ends before the first token at its depth that ends an annotated expression, that is `)` `]` `}` `,` `;` `else`, `END` or `HEAD_END`. Two cases need care: in `@a match y {…}` the inner head's `{` is skipped by the HEAD_END scan first; in `@a if c {…} else {…}` an `else` after a `}` that closes an if-body belongs to the `if`, which bracket matching tells. Nested annotations each get their own token.
2. **One cover grammar for expressions, types and patterns**, read by the parser as one syntax and sorted into the three by a later pass over the tree, as JavaScript parsers do for arrow parameters. This removes causes 1 and 2 above.
3. **Uniform operand levels**: every binary operator's right operand at the next level down, written as recursive nullable tails, as Pareas does; this removes cause 4.

Unary minus (cause 3) and the optional words (cause 5) would remain, each needing a new token or a reserved word. No count after changes 2 and 3 exists, since the checker reads the grammar as written.

## Tests and scaling

All 18 tests of the two modules pass (`zcargo test -p zed-tests --test m0_03_grammar_tools -- llp:: split::`, 2.95 s, load 54).

| Test | Sizes | Instructions | Bytes | Limit |
|---|---|--:|--:|--:|
| the depth scan (`split`) | 2,000 and 16,000 items | 8.0x | 8.0x | 11.2 |
| the split parse (`split`) | 2,000 and 16,000 items | 8.0x | 8.0x | 11.2 |
| the pair table of n nested rules (`llp`) | 200 and 1,600 rules | 8.0x | 7.9x | 12.25 |

Negative controls, run once and not committed:

- the scan looking up cuts by `Vec::contains`, O(n²): 31.3x, fails against 11.2;
- the split parse copying all tokens for each segment: 59.4x the bytes, fails against 11.2;
- the llp core lookup by linear search: 31.2x, fails against 12.25.

## Questions for the author

None is entered in QUESTIONS.md: the split needs no grammar change, and the LLP redesign holds up nothing before GPU-front. When GPU-front is planned, the question is whether to adopt the three changes above, which would give a parse that is parallel inside an item as well as between items; on the corpus an item averages 33 tokens, so between-item parallelism is what the corpus gives.
