# Associativity of the rules of sec:grammar (item LR4)

Each rule of the syntactic PEG (`zed/grammar/syntax.peg`, copied from DESIGN.md sec:grammar)
states its associativity in one of two ways: by left or right recursion, or by a repetition
whose reader folds in the direction the semantics needs. The author's rule (2026-11-03): a
repetition is fine if its reader builds the correct left- or right-nested tree; otherwise the
rule is left- or right-recursive. LR3, which converted repetitions only because they were
chains, was stopped.

**Decision rule.** A repetition stays when long chains are typical and its reader folds the
right way, or when the construct is a list or a conjunction (no nesting to choose). Otherwise
it becomes recursion. A reader that folds the wrong way is a bug, fixed with a test that shows
the wrong nesting first.

**Result.** Two rules were converted: `Expr12` (the `else` chain) and the `&&` chain of
`JoinTerm` (now the rule `AndJoin`). No reader folds the wrong way: the parser, the syntax
tree builder (`crates/zedc-syntax/src/ast/`) and the formatter (`crates/zedc-syntax/src/format.rs`) agree
with the semantics on every row. The tests are in `tests/steps/l01_08_parser/lr4_assoc.rs`
and the bracketing cases at the end of `zed/grammar/cases.txt`.

Line numbers are those of commit LR4 on branch `wt/lr4`. "Not built" means the rule belongs to
a layer after L1: the builder reports the layer (`Builder::later`, `ast/mod.rs:400`), so the
reader that folds it is written by the step named.

## Converted

| Rule | Semantics | Long chains typical? | Form before | Reader and its direction | Decision |
|---|---|---|---|---|---|
| `Expr12` (`a else b else c`) | left: each tail applies to the expression before it | no (2 or 3 tails) | `Or ElseTail*` | `Builder::make_expr` `ast/mod.rs:462` with `else_tail` `:591`, left (it was a left fold over the list); formatter `format.rs:753` writes `of` at its own level and the default one level tighter, so `a else (b else c)` keeps its parentheses | left recursion `Expr12 = Expr12 ElseTail \| ~Or`; a lone operand now leaves no `Expr12` node |
| `JoinTerm` `&&`, `&& ?`, `&& !` chain | left: inner, left and difference joins; difference is not associative, and the kinds mix | no | `KeyTerm ('&&' ('?' \| '!')? KeyTerm)+` | not built (L8: the `into`/`as` tail of `Reduce` reports its layer, `ast/mod.rs:494`) | left recursion `AndJoin = AndJoin '&&' ('?' \| '!')? KeyTerm \| KeyTerm '&&' ('?' \| '!')? KeyTerm`, the base pair as in `TypeDiff`; `JoinTerm = ~AndJoin \| ...` |

## Left recursion already (LR2)

| Rule | Semantics | Long chains typical? | Form | Reader and its direction | Decision |
|---|---|---|---|---|---|
| `Or`, `And` | left (associative) | yes | `Or '\|\|' And \| ~And` | `binary` `ast/mod.rs:469`, `:553`, left; formatter `format.rs:679` (left operand at its level, right one tighter) | keep |
| `Additive`, `Multiplicative` | left | yes | left recursion | as `Or` | keep |
| `Postfix` | left | yes | `Postfix Suffix \| ~Primary` | `suffix` `ast/mod.rs:504`, `:612`, left | keep |
| `Reduce` | left | yes | `Reduce ReduceTail \| ~Range` | `ast/mod.rs:491`, the inner tail first; the L2.1 branch folds `with { }` tails left | keep |
| `Path` | left (a qualified name) | no | `Path '.' Name \| Name` | `TypeName` `ast/types.rs:135` joins the tokens | keep |
| `KeyPath` | left | no | left recursion | not built (L5) | keep |
| `TypeOr`, `TypeAnd` | associative | yes | left recursion | `operands` `ast/types.rs:161` flattens to a list; formatter `format.rs:841` writes the list | keep |
| `TypeDiff` | left (difference) | no | `TypeDiff '\\' TypeNot \| TypeNot '\\' TypeNot` | `ast/types.rs:121`, left; formatter `format.rs:843` | keep |
| `TypePostfix` | left | no | left recursion | not built past one suffix (L10, `ast/types.rs:104`) | keep |

## Right recursion

| Rule | Semantics | Form | Reader and its direction | Decision |
|---|---|---|---|---|
| `Arrow` | right | `TypeUnion '->' Arrow` | `arrow` `ast/types.rs:108`–`:120`, right | keep |
| `Prefix`, `Power` | right | `('-' \| '!') Prefix`, `Postfix '^' Prefix` | `ast/mod.rs:495`, `:503`, right; formatter `format.rs:682` | keep |
| `TypeNot` | right | `'!' TypeNot` | not built (L10) | keep |
| `Lambda` body | right | `... '->' (Block \| Expr)` | `lambda` `ast/mod.rs:566` | keep |
| `If` else-if | right | `'if' ... 'else' (If \| Block)` | `ast/mod.rs:532` | keep |

## Not associative (one operator, no chain)

`Equality` and `Compare` (one operator; a chain is `EqChain`, `AscChain` or `DescChain`),
`IsTest`, `InTest`, `Range`, `Entry`, `TestCase`, `Break`: each takes two operands and does
not repeat. Kept.

## Conjunctions (every neighbor pair compared)

| Rule | Long chains typical? | Form | Reader | Decision |
|---|---|---|---|---|
| `EqChain`, `AscChain`, `DescChain` | sometimes | `Relation '==' Relation ('==' Relation)+` | not built (L22.1); `a < b < c` is `a < b && b < c`, which no nesting expresses | keep |

## Lists

| Rule | Long chains typical? | Form | Reader | Decision |
|---|---|---|---|---|
| `InPattern`, `OutPattern` `('->' X)*` | no | repetition | not built (L8); the levels are listed outermost first and no nested form can be written | keep |
| keys of `IndexedDef`, `KeyedPush`, `BoundaryItem` | no | `('[' Key ']')+` | not built (L6, L7; `ast/stmts.rs:160`); keys listed outermost first | keep |
| `ReduceTail` `Suffix*` after `with`, `as`, `into` | yes | repetition | the L2.1 branch folds left (`reduce_tail`); here not built | keep |
| `TypeFacet*` | no | repetition | not built (L7, `ast/types.rs:103`); facets are a set | keep |
| `MoreGen*` | no | repetition | not built (L5); generators are a list | keep |
| `Update` `('.' Name)*` | no | repetition | not built here; kept by LR2 so the names stay labels | keep |
| `GAlt`, `GSeq` | yes | repetition | not built (L20); alternation and sequence are associative | keep |
| `JoinTerm` `('\|\|' KeyTerm)+` | no | repetition | not built (L8); a full outer join is associative | keep |
| `Level` `SortKey` list | no | `SortKey (',' SortKey)+` | not built (L8); a tuple key | keep |
| `Annot+`, `Trailer+`, `Params`, `Args`, `Boundary` | no | repetition, `%` | `Function` `ast/stmts.rs:175`, `:200`; `args` `ast/mod.rs:646` | keep |
| `JoinExpr` | no | repetition | read only inside a lookahead; builds no node | keep |

## Tests

- `every_rule_of_the_audit_nests_as_its_table_row_says`: one bracketing per row.
- Corner cases: one tail, a name alone, a tail with a pattern mixed with one without, a
  parenthesized `else` on the right (it keeps its parentheses in the formatter), joins of
  mixed kinds, one join, a parenthesized join on the right.
- Scaling at n and 8n (n = 2,000) for the two converted rules and every kept repetition
  above; the building and formatting of a long `else` chain.
- 100,000 `else` tails parsed, built, printed, formatted and dropped, and 100,000 joins
  parsed, on a thread of 8 MiB.
- Negative control, not committed: a reader that folds `else` to the right fails 4 of the 27
  tests (`a else b else c` built as `(else a (else b b))` against `(else (else a b) c)`).
