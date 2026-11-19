# Reusing a running program's state across an edit (STUDY-edit-state-reuse)

Study for plan rows STUDY-edit-state-reuse and SPEC-c15-answer, 2026-11-19, agent editstate1. The spec text it led to is in DESIGN (sec:incremental, "An edit to a running program"; sec:live, "Edits while running"; steps L7.15 and L34.1) and in plan row EDIT-run; this file keeps the reasoning: the sub-problems that have no single right answer, the options weighed for each, the rule chosen, and the cost of each step. The sources are recorded with quotes in verification/bib.md, section "Reusing a running program's state across edits".

## 1. What the author asked

QUESTIONS C15, answered by the author (P346, 2026-11-17), verbatim:

> This is a large researchy problem: figure out how to reuse as much of the running program's frozen state as possible, via keypaths (yes), when a program is modified. If a type of a variable changes, I would say invalidate that value (mark it as "dirty", needing re-flow from inputs or from other state values, and then its downstream transitive closure should also be marked as dirty). If code is removed, there is nothing to pull from the previous run-state. If code and whatever it depends up on has not changed upstream of it, then it can just reuse the old state directly, it probably doesn't even need to look it up by keypath, it can just figure out the old and new storage location for the value(s). Think through this and make a best-effort version of this that works as reliably and predictably as possible, despite the complexity of doing this "right" (in fact there is probably no definition of "right" for many sub-problems of this problem).

C15 itself asked whether row EDIT-run stays before S.1 with a migration given as a run option ("a run option mapping a generation variable's keypath to a function in the edited source, the option kept in the replay record", no grammar change). The answer's "via keypaths (yes)" keeps that; this study gives the option its form.

## 2. What DESIGN said before this study

Sec:incremental, "An edit to a running program", already had: the source as an input port, each edit a wave on it; two readings chosen by a run option, *Replay* (the default: the edited program on the recorded inputs from the first wave, which must equal a from-scratch run) and *Continue* (the edited program from the committed frame of each generation variable, matched by keypath); a migration required wherever a frame's type changes or a generation variable is renamed or removed, and the edit rejected without one; recorded input values that no longer fit an edited port type rejected under Replay; edits kept in the replay record.

What it did not say: what of the old run is reused, and how; what happens to state that depends on a variable whose type changed; how a migration is supplied; what a removed variable needs; what happens to output already written; what happens when a migration fails at run time. The author's answer changes one written rule: a frame whose type changed is no longer a reason to reject the edit, but a value to restart (section 5, sub-problem 4), and a removed variable no longer needs a migration (sub-problem 7).

## 3. Prior work

| System | What it keeps across a change | How a change of shape is handled | What Zed takes |
|---|---|---|---|
| Hazel, fill-and-resume (Omar et al. 2019) | The evaluation state, resumed after a hole is filled | Only hole fills; sound only where evaluation order does not matter | Replay's soundness comes from the from-scratch contract, not from resuming; Continue claims no equality with a fresh run |
| Chordata (Kirisame et al. 2026) | Learned rewrite shortcuts from earlier runs | Not about state; about recomputation | The coarse rule "recompute what is downstream of a change" is the predictable one; its known limit (missed reuse, never wrong reuse) is accepted |
| Edwards, Petricek, van der Storm, Litt 2025 | Survey of schema evolution in live systems | A type change needs a mapping the programmer writes; rename and delete-plus-add cannot be told apart from the text; update at a quiescent point | Restart without a mapping; rename only when the edit says so; edits apply at a wave boundary |
| Dynamic software updating (Hicks and Nettles 2005) | All global state, copied by a state transformer | The programmer writes the transformer; updates at fixed points; a transformer that fails rolls the update back | Migration is an ordinary function; the edit is atomic; a failed migration rejects the whole edit |
| Erlang/OTP `code_change/3` | Each process's state | The callback converts it; the default keeps it unchanged; `{error, Reason}` rolls the release back | Same shape: keep by default, convert by a named function, roll back on failure |
| Nominal Adapton (Hammer et al. 2015) | Memo entries across runs, matched by names | Names chosen by the programmer; ambiguity checked at run time | Zed's fact addresses are names the semantics supplies; matching of unchanged code is structural but exact |
| Meerkat (Liu and Zhong 2024) | State variables | Definitions recomputed from state | The same split: generation variables are state, every other node is recomputed |
| Smalltalk image (via Edwards et al.) | Every object | Class reshaping in the environment | Not read directly; nothing rests on it |

## 4. Two kinds of state

A running Zed program holds two different things, and they need different rules:

1. **Frames of generation variables.** A variable that varies across generations, `x` with `initial x = …; x' = …;` (sec:generations), holds its committed frame between waves. Under Continue this is the only memory the run has of its past, since the recorded inputs are gone. Losing a frame loses information no recomputation can restore.
2. **Derived values.** Every other node's value at a fact address (static node address, dynamic keypath; step L1.20) is a function of the inputs and the frames. Under Replay all of it, frames included, is recomputable from the recorded inputs; keeping it is only a saving of time.

So under Replay reuse is an optimization: it may reuse less but never differently, and the contract "an incremental result equals a from-scratch run" decides every question. Under Continue there is no from-scratch run to equal; the rules there are choices, and each must be predictable and reported.

## 5. The rule in three tiers, and the sub-problems

The author's answer gives three tiers, from cheapest to most expensive:

- **Tier 1, unchanged upstream: direct relocation.** A node whose code and everything upstream of it are unchanged keeps its old values, moved from the old storage location to the new one, with no keypath lookup.
- **Tier 2, changed code, same type: matched by keypath.** A generation variable whose code changed but whose frame type did not keeps its committed frame, found by its keypath (Continue only).
- **Tier 3, changed type: dirty.** A frame whose type changed is marked dirty, with everything downstream of it; under Replay it is recomputed from the inputs, and under Continue it restarts from its `initial` value, unless the edit names a migration for it.

Removed code keeps nothing; added code starts fresh. What follows are the sub-problems where these words leave a choice. Each table is sorted by score (0 discard, 10 perfect); the chosen rule is the first row.

### Sub-problem 1: what "unchanged upstream" means

The node addresses of step L1.20 are positions in the kernel term, and an edit anywhere above a node moves its position, so position cannot decide it.

| Option | Score | Reasoning |
|---|---|---|
| **Upstream hash.** Each node gets a hash of its own elaborated, typed kernel term together with the upstream hashes of its inputs and of every function it calls (a Merkle hash over the dependence graph, cycles hashed as one unit, below). Two nodes match when their hashes are equal *and* a structural check confirms it | 9 | Exact: equal hash plus check means equal code on equal inputs, so equal values on equal inputs. A whitespace or comment edit, or a moved definition, changes nothing. A false match is impossible (the check); a missed match costs only time |
| Source text of the node and its upstream | 5 | Misses every formatting edit and every renamed local, and a change of an imported type does not show in the text |
| Hash alone, with no check | 4 | Correct only up to a hash collision, a claim that cannot be proved, which the standing rule forbids relying on |
| Position in the kernel term | 2 | Any insertion above shifts everything after it, the failure mode memo keys are known for |
| Equality of values, by running both programs | 1 | Needs the run the reuse is meant to save |

The hash is the one step L1.19b already uses for the program's content address. Cycles: a recursive function group (a strongly connected component of the call graph) and the variables of a `loop` that read one another (a component of the loop's dependence graph, including the edge from `x'` to the bare `x` of the step before) are each hashed as one unit, the references inside the unit written as indexes into it in source order. If the members of a unit are reordered the unit hash changes and nothing in it is reused; that is a missed reuse, never a wrong one.

*Cost.* Naive: compare each new node's whole upstream with each old node's, O(n²·s). Chosen: Tarjan's algorithm for the components and one pass in topological order, O(N + E) for N the size of the kernel term and E its edges; the old program's hashes sorted once, O(n log n), and each new node looked up by binary search, O(log n), so O(n log n) in all for n nodes (a hash table gives O(n) expected; the sorted array is chosen for its worst case). The structural check compares a node's own term and checks that each of its inputs is matched to the corresponding input of the old node, which was matched earlier in topological order: O(size of the node's own term + its in-degree), O(N + E) over the program, never a comparison of whole upstream cones.

### Sub-problem 2: what direct relocation does with storage

The author's "figure out the old and new storage location". The planner may lay out a node's storage differently in the edited program even when the node is unchanged (a layout is a plan choice, sec:duality).

| Option | Score | Reasoning |
|---|---|---|
| **Adopt the old buffer when the layout is equal; repack it (a witnessed repack, sec:duality) when it differs** | 9 | Zero copy in the common case; a layout change costs one pass over the values, linear in their size |
| Always copy | 6 | Simple, but pays a full pass even when nothing moved |
| Force the edited program's plan to keep the old layout | 4 | Lets an edit's history change the plan of the new program, so the same source plans differently depending on how it was reached; against deterministic checking |

### Sub-problem 3: when a type counts as changed

| Option | Score | Reasoning |
|---|---|---|
| **The elaborated types differ** (types compared after aliases are expanded, so renaming an alias is no change) | 8 | The author's rule, decided per variable before the run continues, and the report can name the old and new type |
| Each old value is kept when it is a member of the new type, as the Replay rule for recorded inputs does | 7 | Reuses more (a widened range keeps its values) but makes the outcome depend on the values, so one edit may keep a frame in one run and restart it in another; and a member of the new type may mean something else under it (a unit or a facet that changed meaning). Recorded *inputs* use membership because the edited program would have received exactly those values; a frame was computed by the old code |
| Representation equal (same bytes) | 2 | Keeps values whose meaning changed |

### Sub-problem 4: what Continue does with a dirty frame

The author: invalidate it, "needing re-flow from inputs or from other state values". Under Continue the old inputs are gone, so the only re-flow is from the edited program's own start for that variable.

| Option | Score | Reasoning |
|---|---|---|
| **Restart it: evaluate its `initial` expression at the edit's wave in the edited program, reading the kept frames and that wave's inputs; name it in the edit's report** | 8 | The author's re-flow; predictable (the value is what the source says the variable starts at); never silent |
| Reject the edit, as DESIGN said before | 5 | Predictable, but the author asked for invalidation, and a rejected edit leaves the programmer no way forward except writing a migration they may not want |
| Keep the old value if it happens to fit the new type | 3 | Value-dependent (sub-problem 3) |
| Re-flow from a retained window of recent inputs | 3 | Needs a retention the run does not have under Continue; a window size is a threshold |

A migration (sub-problem 8) replaces the restart for the variables it names.

### Sub-problem 5: how far dirtiness spreads under Continue

The author: "its downstream transitive closure should also be marked as dirty". Derived nodes are recomputed every wave anyway, so the question is only which other *frames* restart.

| Option | Score | Reasoning |
|---|---|---|
| **Every generation variable that reads a dirty one, directly or through derived nodes, in the edited program, is dirty too, closed transitively; a migrated variable is not dirty and does not spread** | 8 | The author's rule. Invariant it keeps: no kept frame was computed from a frame that was restarted. Edges are read from the program the programmer is looking at, so the report can explain each restart in its terms |
| The same over the old program's edges, or over both | 6 | Can restart a variable the edited code no longer connects to the change, and explaining it needs the old program |
| Stop at generation variables: only the changed variable restarts | 4 | Mixes a restarted value with frames accumulated from the old one: in `loop { initial n = 0; n' = n + 1; initial sq = 0; sq' = sq + n * n; }`, restarting `n` but keeping `sq` leaves `sq` holding squares of the old counts beside a count started again |

*Cost.* One traversal of the edited program's dependence graph from the dirty variables, with a visited set (the wave-counter stamp of sec:incremental), O(n + e). Naive: a separate reachability search from each dirty variable, O(d·(n + e)).

### Sub-problem 6: a changed step with an unchanged type, under Continue

| Option | Score | Reasoning |
|---|---|---|
| **Keep the frame, matched by keypath (tier 2)** | 9 | What Continue is for: fixing a step and carrying on. The author's "via keypaths (yes)"; DESIGN already said it |
| Restart it as dirty | 3 | Every edit to a variable would lose its state |

### Sub-problem 7: removed, added and renamed variables

| Option | Score | Reasoning |
|---|---|---|
| **A removed variable's frames are dropped and named in the report; an added one starts from its `initial` value; a rename is a removal and an addition unless the edit names it with a migration (sub-problem 8)** | 8 | The author: "If code is removed, there is nothing to pull". Renames cannot be told from a deletion and an addition by the text (Edwards et al.), and guessing would sometimes carry a value into a variable that means something else |
| Detect renames: a removed and an added variable with the same type and step | 4 | A heuristic; two counters of the same shape would be confused; the outcome would change with unrelated edits |
| Require a migration for every removal, as DESIGN said before | 3 | A function from the old frame to nothing; makes deleting code harder than writing it |

Dropping or adding a variable does not make other variables dirty: a variable that read the removed one, or now reads the added one, has had its code changed and is kept by tier 2. Only a type change without a migration spreads (sub-problem 5).

### Sub-problem 8: the form of a migration

C15 recommended a run option. It must name the new variable, the function, and, for a rename or a merge, the old variables it reads.

| Option | Score | Reasoning |
|---|---|---|
| **One run option, `--migrate`, in three forms: `--migrate count=f` (the function of the edited source applied to the old frame of `count`), `--migrate total=f(count)` (applied to the old frames named in the parentheses, in order, so one old variable can feed two new ones and two old ones one new one), and `--migrate total=count` (a rename keeping the value; the types must be equal). The variable is written as the source names it, block names joined by `.`; the options are recorded with the edit in the replay record** | 8 | No grammar change; covers change of type, rename, split and merge; each function is ordinary code checked like any function, its parameter types the old frames' types and its result the new frame's type |
| A source form `@migrate` | 4 | A language word for something used once per edit and then dead in the source |
| A function of the whole old state, as Hicks and Nettles' state transformer | 4 | Most general, but the programmer must rebuild every variable, and the checker cannot tell which frames it reads |

Instances: a migration applies to each instance keypath present in the new variable and in every old variable it names (for a variable inside a family, key by key); an instance missing from one of the old variables starts from `initial`. If an old frame's type cannot be written in the edited source, because the edit removed the type's name, the parameter is written as the structural type. A type that cannot be written in the edited source even structurally exists today, and the rule for it is the first decision of section 9.

### Sub-problem 9: a migration that fails at run time

A migration checked like any function cannot return a value outside its result type, so the only run-time failures are those any call can have (resource exhaustion, `#bug`).

| Option | Score | Reasoning |
|---|---|---|
| **The edit is atomic: if any migration fails at any instance, the whole edit is rejected, the run continues on the old program, and the report names the variable, the instance keypath and the failure** | 9 | Hicks and Nettles roll back for the reason they give (a partly migrated state is corrupt); Erlang does the same. The old frames are still there, since migrations write new storage |
| Restart the failed instances | 5 | Turns a bug in the migration into silent loss |
| Apply the migrations that succeeded | 2 | A mixed state no single program would produce |

### Sub-problem 10: when an edit takes effect

| Option | Score | Reasoning |
|---|---|---|
| **At a wave boundary: the edit is a wave on the source port, ordered after the wave in flight, as every arrival is** | 9 | Already DESIGN's model; Hicks and Nettles' "update points" and Edwards' "quiescent point"; a wave is never split, so no frame is half committed |
| At once, inside a wave | 1 | A frame computed partly by each program |

### Sub-problem 11: output already written

Under Replay the edited program's past waves can produce outputs that differ from what the old program wrote.

| Option | Score | Reasoning |
|---|---|---|
| **Outputs for waves before the edit's wave are computed and compared, not written again; the run reports, per output port, the first difference, as `zedc replay --program` does (step L1.19d); outputs from the edit's wave on are written** | 8 | The world cannot be unsent to; a display that shows the past (sec:live) reads the recomputed values like any other reader |
| Write the recomputed past outputs again | 2 | Sends a second copy of everything to every port |
| Recompute no output before the edit's wave | 4 | Then a past frame shown in the editor would not match the edited program |

### Sub-problem 12: reuse under Replay

| Option | Score | Reasoning |
|---|---|---|
| **Tier 1 at every fact address: a node matched by sub-problem 1 keeps its old value at each keypath the old run had, across all waves, frames included; every other node is recomputed, with the compare-before-propagate cutoff** | 9 | Sound because the recorded inputs are the same, so a node with the same code on the same upstream has the same value at each fact address; whether the instance set changed (a loop's guard edited) does not change the value of an instance both runs have. What is kept is a plan choice by cost, as retention is (sec:security), never a meaning |
| Recompute everything | 5 | Correct; the cost the author wants avoided |
| Reuse by keypath alone, ignoring code changes | 0 | Wrong values |

## 6. How it fits Replay, Continue and the migration text

- *Replay* is unchanged in meaning: the result is a from-scratch run of the edited program on the recorded inputs. This study adds only how much is kept (sub-problems 1, 2, 12) and what happens to past outputs (sub-problem 11). A recorded input that no longer fits an edited port type is still rejected, as before; that changes the port node's hash, so everything downstream of it is recomputed.
- *Continue* changes in two places the author's answer decides: a frame whose type changed and has no migration restarts (with the variables that read it) instead of rejecting the edit, and a removed variable is dropped without a migration. The report of a continued edit lists, in source order, every variable restarted (with the variable whose type change caused it), dropped, added, migrated and renamed, so nothing happens silently (no surprises, P239).
- *Migrations* get their form, the `--migrate` run option, kept in the replay record, so a recording with edits replays bit-exactly (step L1.19b's address check applies to each edit wave's program address).

Spec changes made from this study: sec:incremental "An edit to a running program" rewritten with the rules above; sec:live "Edits while running" brought into line; step L34.1's test extended (restart and spread, removal, rename, split and merge, failing migration, past outputs, reuse); step L7.15 names the edit test of row EDIT-run.

## 7. Total cost of applying one edit

For an edited program of kernel size N with E edges and n nodes, m committed frame instances, and b bytes of relocated storage whose layout changed:

| Step | Cost | Naive alternative |
|---|---|---|
| Upstream hashes of the edited program | O(N + E) | per-node comparison of whole upstream cones, O(n²·s) |
| Matching old to new nodes | O(n log n) worst case, sorted array and binary search | all pairs, O(n²) |
| Structural check of matches | O(N + E) | whole-cone comparison per match, O(n·N) |
| Dirty closure (Continue) | O(n + e), one traversal with a visited set | one search per dirty variable, O(d·(n + e)) |
| Frame matching by keypath (Continue) | O(m) when frames are stored in keypath order, O(m log m) otherwise | per instance search, O(m²) |
| Migrations | the migrations' own cost, once per instance | none |
| Relocation | O(1) per adopted buffer, O(b) for repacked ones | always copy, O(total size) |

All steps are linear or n log n in the size of the program and of the state; the scaling test of row EDIT-run checks T(8n)/T(n) for programs of n and 8n nodes and for n and 8n frame instances.

## 8. Tests that row EDIT-run and step L34.1 need

Under Continue:
- `loop { initial n = 0; n' = n + 1; initial big = 0; big' = if n > 10 { big + 1 } else { big }; }` edited to `initial n = 0.0; n' = n + 1.0;` and `n > 10.0`, so `n` changes from `int` to `f64` and `big` stays `int`, with no migration: `n` and `big` restart from their `initial` values at the edit's wave, and the report names both, `big` as reading `n`. With `--migrate n=widen`, where the edited source defines `widen(positional old: int) = f64(old);`, neither restarts.
- A step edited with the type unchanged keeps the frame.
- A removed variable is dropped and named; an added one starts from `initial`.
- A rename with `--migrate total=count` keeps the value; without it `count` is dropped and `total` starts fresh.
- A split (`--migrate a=f(p)` and `--migrate b=g(p)`) and a merge (`--migrate t=h(a, b)`).
- A migration that fails at one instance of a family rejects the whole edit, the run continues on the old program, and the report names the variable, the key and the failure.
- Variables inside a family: a key in both runs keeps its frame, a key only in the old run is dropped, a key only in the new one starts fresh.

Under Replay:
- Each frame equals a fresh run of the edited program on the recorded inputs (as before), and outputs before the edit's wave are reported, not written again.
- Reuse: an edit to one of two independent loops recomputes only that loop (counted by the interpreter's node evaluations), and a comment-only or formatting edit recomputes nothing.
- A reordered recursive group is recomputed and gives the same values (a missed reuse is never a wrong one).

Both: replaying the recording with its edits and `--migrate` options reproduces the run bit-exactly.

## 9. The two points this study left open, decided

This section first listed two open points. Plan row EDIT-reuse-open-points (agent docs3, 2026-11-19) decided both by the standing rules (exact answers, no surprises, deterministic checking); the spec text is in DESIGN sec:incremental, "An edit to a running program", and the tests in step L34.1.

### Decision 1: a frame type the edited source cannot write

The first open point said that "every frame type is writable" until nominal types arrive. That is not so today. Two kinds of type are named by something an edit can take away:

- An opaque atom of a predicate refinement is named by its syntax tree with each call resolved to the content address of its definition (DESIGN sec:domains). So the old frame type `(x: int where isOdd(x))` names the old `isOdd`. If the edit removes `isOdd`, no source can name that atom. If the edit changes the body of `isOdd`, the same text in the edited source names a different atom, so the frame type changed (tier 3) and `int where isOdd(old)` written in the migration is a different type, which the old frame is not known to be a member of.
- A grammar type (`type Ident = Utf8String matching grammar { … }`) is related to other types only nominally (DESIGN sec:domains), so an edit that removes or changes the grammar leaves the old type with no name in the edited source.

| Option | Score | Reasoning |
|---|---|---|
| **The parameter type of a migration is any type of the edited source that the old frame's type is a subtype of, checked by the ordinary subtyping procedure with the old type taken from the old program; the old type itself, where it can be written, is one such type. A migration whose parameter is not a supertype of the old frame's type is rejected when the edit is checked, naming both types. Where the migration needs the old refinement's fact, the repair is to keep the definition for one edit, migrate, and remove it in the next** | 9 | Exact: the subtyping is the one the checker already decides, so every compiler gives the same verdict. The base of a refinement (`int` for `int where isOdd(x)`, `Utf8String` for a grammar type) is a supertype the edited source can always write, so a migration always exists for a frame of data. No new form. Nothing is accepted that could hold a value outside the parameter's type |
| Require the parameter type to equal the old frame's type (the rule before) | 3 | Leaves a frame whose refinement named a removed function with no migration at all, so the only choice is a restart, which loses the frame silently from the programmer's point of view |
| Let the migration's parameter take the old type by a special name (`old.type`) | 4 | A new form used once per edit; messages would have to print a type the program cannot write, which the standing rule forbids (printed types are syntax) |
| Check the parameter type only at run time, frame by frame | 1 | A check that can fail after the edit is accepted: a surprise, and a refinement with an opaque atom cannot be checked on a value by the checker at all |

A frame type with a refinement under a function's parameter, as `((x: int where isOdd(x)) -> int)`, has no writable supertype that can be called, since a supertype of a function type takes a subtype of its parameter. Such a variable restarts (tier 3) when no migration names it, as every variable whose type changed does; a migration of it is rejected by the rule above, with the repair of keeping the definition for one edit. Messages print the old type as the old source wrote it, so every type a message prints is one the programmer wrote.

### Decision 2: the run options in the upstream hash

The upstream hash covers the elaborated term of a node, so a run option that changed a value without appearing in that term would make a hash match reuse a stale value. Each run option was checked against DESIGN:

| Option | Changes a value? | Why the hash is right |
|---|---|---|
| `--option <name>`, the build's target | yes | `build.options.<name>` and `build.target` become literals at resolution, so they are in the elaborated term and in the content address (DESIGN, step L2.8d). Measured: a record of a run that reads `build.options.fast` replays only with the same `--option` words; a record of a program that reads no option replays with any (test `a_record_replays_only_with_the_options_its_program_reads`, tests/steps/l02_08d_build_constant/command.rs) |
| The floating-point environment | no option sets it | bit-identity pins round-to-nearest-even, no contraction and no extended precision (DESIGN sec:reduction), and foreign code cannot change it for Zed code (sec:ffi, plan row FFI-fpenv) |
| The grouping of a reduction of a reorder-faceted value | no option sets it | the grouping a run used is recorded, and the value is re-derived only from its recorded grouping (sec:reduction), so a kept node keeps its grouping with its value |
| `--strict`, `--total`, `--suppress` | no | they accept or reject a program, or silence a warning; a program they accept computes the same values |
| `--record`, `--bench`, `--leak-check`, `--explain-plan`, `--addresses`, `--c-library`, `--program` | no | they choose what is written beside the run, how it is built, or which program a record is checked against |
| `--migrate` | yes, under Continue | it is an edit's own input, recorded with the edit in the replay record; it applies to frames, not to nodes the hash matches |

| Option | Score | Reasoning |
|---|---|---|
| **No run option changes a value outside the term: state this in DESIGN as a closed list; a later option that changes values is written into the term at resolution, as `--option` is, or hashed with the term** | 9 | Exact today, checked option by option; keeps one hash for the address and the reuse; the rule tells the author of a new option what to do |
| Hash the whole command line into every node | 4 | Correct but throws away every reuse when an unrelated word (`--record out2.rec`) changes, and makes the reuse depend on spelling |
| Hash a fixed list of option values into every node | 5 | Correct, but a node that does not read `build.options.fast` would still be recomputed when it changes; the term already carries what each node reads |

### The amount kept is not a meaning

DESIGN says that how much an edit keeps under Replay "is a plan choice by cost, never a meaning". Step L34.1's test now checks it: a run whose plan keeps nothing gives the same frames, outputs and report as one whose plan keeps every matched node.
