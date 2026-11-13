# Facet-ops study: facets through operations, removal, casts and logarithmic units

Item FACET-ops-study, 2026-11-11. This file keeps the study behind the DESIGN.md changes of the zed spec commits named in the ledger line of FACET-ops-study: P13 in sec:pillars, the paragraphs "Annotations are facets", "The algebra of units", "Kinds", `UnitText`, "Logarithmic units", "Removing a fact" and "Facts through operations and casts" in sec:facets, rule `ReduceTail` in sec:grammar, six rows of sec:diagnostics, and plan steps L12.2h to L12.2k. The implementation is plan rows L12.2h, L12.2i, L12.2j, L12.2k and FACET-ops-tests of `docs/plan_dag.md`. Claims are marked [C] (confirmed, with the source named) or [I] (inferred, with what would confirm it).

## The question

The author's request, verbatim:

> `two facts of one word, such as units("m") and units("s") on one value` -- consider how to handle cases like this. Presumably it should be an error to declare different unequal units on the same value twice -- so should facets have a specifier that says that they can only be applied once? Can you think of valid cases where the same facet may need to be added more than once to a value, with a different facet param in each? Java has the concept of "repeated annotations", which was added a few releases after annotations were added, so there must be reasons to do this (research them and see if it's justifiable). If we ban the repeated use of any facet on a value, then that settles the units question, but if it's deemed optional to declare a facet as being able to be repeatedly applied, then we need to think about the semantics of how that would work (I tend to think it will just overcomplicate everything). Another thing to consider: there probably needs to be a way to remove facets -- maybe `without units` should remove the units facet. (This would also be more complex if repeat facets were allowed, because you'd have to be able to specify which one of more than one that you wanted to remove.) The reason this would be needed is because casting a value that has units from say int to f64 should probably preserve the facets of the value through the cast -- is that true? Think deep and hard about this, because it is important to get this right. And casting is just one type of operation: we already have to have special behavior for combining units when doing multiplication or division or exponentiation or taking the log of a number that has a units facet. Think about all other types of operations that can be done with any of the built-in value types, consider what facets may be used with the value, think about what operations would typically be done to the value, and think about how or whether the facets should bubble through the operation, optionally with specialcasing (like the unit-combining case). Do this as a detailed study, weigh options, and then do the most sensible thing. Also, speaking of log -- we do need to support log in the units notation too, with parens: e.g. `log(5 with units("m"))` gives 5 with units `log(m)`.

The last sentence is read as `log(5 with units("m"))` giving ln 5, about 1.6094, with units `log(m)`: the value of `log(x)` is the logarithm of the number, and only the unit text keeps the word `log`. Nothing in the request requires the result to be 5.

## The author's decisions during the study (2026-11-11)

The coordinator relayed these while the study ran; they are settled and are recorded here, not scored again.

1. **Repetition:** keep the ban. Java's repeatable annotations are shorthand for one array-valued annotation; the study records the research (section "Repetition" below).
2. **Removal:** `x without units("km")`, never a bare `without units`. DESIGN presents it as an example of the standing rule, in the author's words: "everything in Zed must be explicit, that there must be no surprises to the programmer, and that all classes of runtime error that can possibly be caught must be caught." DESIGN's principles had no such rule, so it was added as pillar P13 with the author's name and the date.
3. **The five classes of facet and their defaults** are approved: quantity facts are kept by casts, changed by arithmetic, and an operation with no rule rejects rather than drops; flow facts are joined; representation facts belong to the carrier, so a cast takes the target's; evidence facts are dropped unless proved; hints are recomputed or dropped. Casts keep units.
4. **Logarithmic units** are approved and are valid in all three places: the `UnitText` grammar (`log`, `log2`, `log10`), the transfer through `log` and `exp`, and display. The author's reason: "in data visualization, it is common to plot using log(x) and/or log(y), and the units in that case are shown as log(m) etc." Rule 4 of "Kinds" changes to match. The algebra is approved; the decibel, the neper, pH and soundness were still to be checked, and are checked below.

## Evidence

- **JEP 120, Repeating Annotations** (Java 8), https://openjdk.org/jeps/120 [C, read 2026-11-11]. Motivation: "Frequently-used idioms of programming with annotations in EE and elsewhere awkwardly use a container annotation just to simulate the ability to apply multiple annotations." Description: "desugar repeated annotations of a base type into a single container annotation; the container annotation has a values method which returns an array of the base annotation type." So the feature is syntax for one annotation whose element is an array.
- **JLS §9.6.3 (Repeatable Annotation Interfaces) and §9.7.5 (Multiple Annotations of the Same Interface)**, https://docs.oracle.com/javase/specs/jls/se21/html/jls-9.html [C, read 2026-11-11]. §9.7.5: "If a declaration context or type context has multiple annotations of a repeatable annotation interface A, then it is as if the context has no explicitly declared annotations of interface A and one implicitly declared annotation of the containing annotation interface of A", and "The elements of the (array-typed) value element of the container annotation are all the base annotations in the left-to-right order in which they appeared in the context." Repeated annotations beside a hand-written container are a compile-time error.
- **C# `AttributeUsageAttribute.AllowMultiple`**, https://learn.microsoft.com/en-us/dotnet/api/system.attributeusageattribute.allowmultiple [C]: an attribute class opts in, and reflection then returns several attribute objects. That the common uses (several author names, several conditional symbols, test-case attributes) are each a list of values of one kind is [I], from common use rather than a survey.
- **F# units of measure**, https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/units-of-measure [C]. A unit is removed with `float x` or by dividing by `1.0<degC>`, and attached by multiplying by `1.0<m>` or with `LanguagePrimitives.FloatWithMeasure`. Units are erased at run time, so "implementing a `ToString` function to print out the units is not possible."
- **Haskell `dimensional`**, https://hackage.haskell.org/package/dimensional/docs/Numeric-Units-Dimensional.html [C]. `v = 90 *~ (kilo meter / hour)` attaches a unit, and "the numerical value of a quantity is `numval = v /~ (meter / second)`": the unit is named where it is removed, and a wrong one is a type error. Its `log`, `sin` and `log1p` have type `Dimensionless a -> Dimensionless a`.
- **Kennedy**, "Types for Units-of-Measure: Theory and Practice", CEFP 2009, LNCS 6299, and his 1996 thesis "Programming Languages and Dimensions" (University of Cambridge Computer Laboratory technical report UCAM-CL-TR-391, https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-391.pdf), cited from memory and not re-read for this study [I]: units as an abelian group, unification over ℤⁿ (ℚⁿ with rational powers), and the parametricity theorem that a function generic in a unit cannot depend on the unit's choice. The rule "a unit variable never stands for a logarithmic unit" below rests on that theorem.
- **SI Brochure, 9th edition (2019)**, https://www.bipm.org/documents/20126/41483022/SI-Brochure-9-EN.pdf [C, text extracted with pdftotext]:
  - Table 8, note (m): "The neper, bel and decibel are used to express values of specified logarithmic ratio quantities. When using these units, it is important that the quantity be specified, and that any reference value used be specified." The table defines "LX = m dB … m = 10 lg(X/X0)" and "LA = n Np … n = ln(A2/A1)".
  - 5.4.1: "p = 48 kPa may equally be written as p/kPa = 48": the number of a quantity is the quantity divided by its unit.
  - 5.4.3: "a space is always used to separate the unit from the number", except for the angle symbols °, ′ and ″; "t = 30.2 °C". On %: "a space separates the number and the symbol %".
- **ISO 80000-3:2019 and IEC 60027-3:2002** (logarithmic quantities and their units): not read; both are paywalled and the SI Brochure's Table 8 note (m) states the rule they give for the neper, bel and decibel [I: confirming needs the ISO or IEC text].
- **Molyneux, "The Système International d'Unités and the logarithmic units"**, Metrologia 28 (1991), and **Matta, Massidda, Kurinami et al.** on "logarithmic units" and angles: cited for the long dispute over whether a logarithm can carry a unit at all. Not read in full [I]; the study does not depend on them, since Zed's `log(m)` is the unit of the logarithm of a number counted in metres, a label that changes by an offset with the unit, not a claim that the SI admits it.

## Repetition (settled by the author: keep the ban)

| Option | Score | Reason |
|---|---|---|
| Keep the ban: one fact per facet word; a fact that needs several values takes a list or set argument | 10 | A value carries one element of each facet's lattice, so two facts of one word either meet (and the second is redundant or contradicts the first) or are one fact with a collection. Java's repeatable annotations are that collection as sugar (JLS §9.7.5), and every C# `AllowMultiple` use read is a list of one kind. Zed already writes `units([…])` and `names(…)` with one argument per level. |
| A `repeatable` field on `Facet`, facts kept in written order | 3 | Gives nothing a list argument does not, and `without` would then have to name which of several facts it drops, as the author noted. Order of facts on one value would become meaning, which no other part of Zed has. |
| Repetition allowed for every facet, the facts met in the lattice | 2 | `units("m")` with `units("s")` would meet to the empty element and reject anyway, one step later and with a worse message; for a facet whose meet is a join of sets it is the list argument again. |

No use was found that a list or set argument does not cover: per-instance targets do not arise, since a Zed fact sits on one value or type and a level's facts are one list; JSR 308 type annotations repeat on one type position by the same container rule (JLS §9.7.5 applies to type contexts too [C]); Rust `#[derive(A, B)]` is one attribute with a list; Python decorators applied twice are two function wrappers, which Zed writes as two calls.

DESIGN change: "Annotations are facets" now says no facet declares itself repeatable and gives the reason with the Java evidence.

A related rule the study found missing: a fact derived through an operation counts as a fact on the value. So `(d / t) with units("m/s")` is a check, and `(d / t) with units("km/h")` is rejected with `(d / t).to("km/h")` in the menu, row "Fact written on a value that carries a different one". Without this rule `with` on a derived value would have no stated meaning: either a second fact of one word (banned) or a silent replacement (a unit change with no conversion).

## Removal (settled by the author: `x without units("km")`)

| Option | Score | Reason |
|---|---|---|
| `x without units("km")`: the fact named in full, checked present, then dropped | 10 | The reader sees at the drop what number comes out; if `x` is later declared in `m`, the drop is rejected rather than silently giving metres read as kilometres (P13). It is `dimensional`'s `/~ unit`, with a word that works on `int` too. |
| Division by one unit, `x / (1.0 with units("m"))` | 7 | Already valid on floats and `rat` (SI 5.4.1: `p/kPa = 48`) and kept; but `int` has no `/`, and it removes only units, not `names` or `order`. |
| Bare `x without units` | 3 | Drops whatever unit is there, so a change of the declared unit changes every number read after it with no message: the class of error P13 says must be caught. |
| No removal | 2 | `int` values with units could never be printed as plain numbers, passed to a function with no unit, or given a different unit. |

Which facets allow `without` (field `removable: bool = false` of `Facet`, true for `units`, `names` and `order`):

| Facet | `without` | Reason |
|---|---|---|
| `units` (with kinds, point and logarithmic units) | yes | Reading the number of a quantity in a named unit is normal (SI 5.4.1). |
| `names` | yes | Level names are labels; a program that wants positional levels says so. |
| `order` | yes | An order on a type is a choice of the program; dropping it removes comparisons, which the checker then reports at any use. |
| `taint` | no | Lowered only by a named sanitizer (sec:security); `without` would be a trust bypass. |
| laws (`associative`, `commutative`, `idempotent`, `injective`) and `cost`, `fused`, `memoized`, `noalloc`, `preallocated` | no | Each is a claim about code; dropping the fact does not make the claim false, and a program that does not want it checked does not write it. |
| `bits`, `endian`, `layout`, `store`, `reducer` | no | Facts of a declared type or declaration: a value gets other ones by a cast to another type or another declaration. |

Grammar: `'without'` joins `KeywordWord` (L1), and rule `ReduceTail` gains `| 'without' FacetCall Suffix*` at L12, beside `'with' FacetCall Suffix*` (L7). `without` binds as `with` does, so `a + b without units("m")` drops the unit of the sum, and `x without units("m") with units("s")` is `(x without units("m")) with units("s")`. A bare `n without units` is a parse error (expects `(`). Grammar cases for all of these are in `zed/grammar/cases.txt` [C: `cases` tool, 530 cases, 0 wrong].

## Defaults through operations

| Option | Score | Reason |
|---|---|---|
| No new field: the last `_` arm of each facet's `transfer` is its default; DESIGN states the default of each of five classes | 10 | `transfer: (_, (E,) \| (E, E)) -> E` already maps every operator atom, and its final arm is what an operation it does not name gets [C: the `Facet` struct in sec:facets]. Nothing new to check or print. |
| A field `default: #keep \| #join \| #drop \| #reject` | 5 | Duplicates the `_` arm and could disagree with it; one more thing the checker must reconcile. |
| One default for all facets (drop) | 2 | Dropping a unit silently is exactly the error units exist to catch. |

The five classes (DESIGN "Facts through operations and casts"):

1. Quantity facts (`units`, kinds, point units, logarithmic units): a rule for each built-in operation; an operation with no rule accepts only values with no unit fact or in `1` with no kind.
2. Flow facts (`taint`): the join of everything the operation reads.
3. Representation facts (`bits`, `endian`, `layout`, `store`, `reducer`): those of the result's declared type; a cast takes the target type's.
4. Evidence and hint facts (laws, cost facts, a program's own): the top of the lattice unless the facet's transfer names the operation and its `transferSound` law is proved; a hint the compiler derives (`f::cost`) is derived again.
5. Level facts (`names`, `order`): follow the levels through `as`, `into`, joins and reductions; an operation on entries does not touch them.

## Casts

| Option for a cast between number types | Score | Reason |
|---|---|---|
| Keep every quantity fact (operator atom `#cast`) | 10 | `f64(n)` with `n` in `m` is still a length in metres; DESIGN's Kinds rule 2 already said casts keep the kind [C]. |
| Drop units at a cast | 1 | A cast to read a number in another carrier would silently become a unit removal, the error `without` was made explicit to prevent. |

| Option for a cast to `Utf8String` (`"${x}"`, `Utf8String(x)`) | Score | Reason |
|---|---|---|
| Write the number, one space, then the unit text; no space before `°`, `′`, `″` as angles | 8 | What a reader of the output needs, in the SI's spelling (5.4.3); `"${n without units("m")}"` writes the bare number, explicitly. |
| Reject a cast to string of a value with a unit | 6 | Safe, but every log line and table cell would need a `without`. |
| Drop the unit | 2 | The F# behavior, forced there by erasure; Zed knows the unit statically. |

A cast from a string (parsing) gives no unit fact; the program attaches one with `with units(t)`. Taint joins through every cast.

## The operation table

Which prelude facets can sit on which built-in types [C: DESIGN sec:facets, sec:security, sec:level_names, sec:order]:

| Type | units (kinds, point, log) | taint | names | order | bits, endian, layout, store | reducer | laws, cost facts |
|---|---|---|---|---|---|---|---|
| int domains, `rat`, `f32`, `f64` | yes | yes | — | — | yes (bits, endian) | — | — |
| `bool`, atoms | — | yes | — | atoms with `order` | — | — | — |
| `Utf8String` and views | — | yes | — | — | layout | — | — |
| tuples, structs | per field | yes | — | — | layout, store | — | — |
| maps, sequences, tensors | per level (`units([…])`) | yes | yes | yes | layout, store | yes (accumulators) | — |
| functions | on the result type | yes (`@taint`) | — | — | — | — | yes |
| `Instant`, `Duration` | `s` by type | yes | — | — | — | — | — |

What each operation does to each class (quantity facts in detail, since the other classes follow their default):

| Operation | Quantity facts | taint | names, order | representation | evidence, hints |
|---|---|---|---|---|---|
| `+`, `-`, `min`, `max`, `clamp`, `mod`, `gcd`, `hypot` | equal units required, kept (DESIGN before this study, extended to `mod`, `gcd`, `hypot`, `clamp`) | join | untouched | declared type's | top unless proved |
| `*`, `/`, `div` | units multiplied, divided | join | untouched | declared type's | top unless proved |
| `^` | integer or rational constant power; else `1` (DESIGN before) | join | untouched | declared type's | top unless proved |
| negation, `abs`, `floor`, `ceil`, `round`, `trunc` | kept, kind kept | join | untouched | declared type's | top unless proved |
| `fma(a, b, c)` | unit of `a * b + c` | join | untouched | declared type's | top unless proved |
| `==`, `<` and the comparisons, `isNaN` | equal units required; result `bool` with no unit | join | untouched | — | — |
| `shl`, `shr` | unit of `x` kept; `k` in `1` | join | untouched | declared type's | top |
| `bitAnd`, `bitOr`, `bitXor`, `popcount` | operands in `1` | join | untouched | declared type's | top |
| reduction by `+` | kept | join | level removed | — | top |
| reduction by `*` | `u^n` when `n` is a compile-time constant, else `1` required | join | level removed | — | top |
| `sqrt`, `cbrt` | half, third power (DESIGN before) | join | untouched | declared type's | top |
| `exp`, hyperbolic | `1` with no kind | join | untouched | declared type's | top |
| `log`, `log2`, `log10` | `1`, or a unit with no kind and no point unit → `log_b(u)` (new) | join | untouched | declared type's | top |
| trigonometric | `1` or `rad`, no kind (DESIGN before) | join | untouched | declared type's | top |
| `.to(t)` | converted (DESIGN before, extended to log units) | join | untouched | declared type's | top |
| casts between number types | kept (`#cast`) | join | untouched | target type's | top unless proved |
| cast to `Utf8String` | written into the text | join | — | target type's | top |
| parse from a string | none | join | — | target type's | top |
| `len`, indexing, slicing, concatenation | `len` has no unit; an entry keeps its level's unit | join | follow the levels | declared type's | top |
| hashing | none | join | — | — | — |
| `matmul` | products summed: the units of `a[r][c] * v[c]`, equal over `c` (sec:linalg) | join | follow the levels | — | top |

## Logarithmic units

### The algebra

A logarithmic unit is a base b ∈ {e, 2, 10} with an exponent vector v ∈ ℚⁿ, written `log_b(u)` where `u` has vector v. A value y in `log_b(u)` stands for the quantity b^y in u. The identity everything rests on: for x in unit u and a unit u' = c·u (c a positive constant),

  log_b(x counted in u) = log_b(x counted in u') + log_b(c).

So changing the unit inside the logarithm moves every value by the constant log_b(c). An operation is accepted exactly when its result moves by a constant that the units fix.

| Rule | Unit of the result | Why it is sound |
|---|---|---|
| `y1 + y2`, `y1` in `log_b(u)`, `y2` in `log_b(w)` | `log_b(u w)` | log x + log z = log(x z); the result moves by log c_u + log c_w = log(c_u c_w), the constant of `u w`. |
| `y1 - y2` | `log_b(u/w)`; `log_b(1)`, which is `1`, when u = w | log x − log z = log(x/z). |
| `y + k`, k in `1` | `log_b(u)` | multiplying the quantity by b^k, a number with no unit. |
| `-y` | `log_b(1/u)` | −log x = log(1/x). |
| `k * y`, k an `int` or `rat` constant or a decimal literal | `log_b(u^k)` | k log x = log(x^k); moves by k log c, the constant of u^k. A run-time k moves by an amount the program does not fix: rejected. |
| `y / k`, k a nonzero constant | `log_b(u^(1/k))` | as above. |
| `==`, comparisons, `min`, `max` | same unit required | both sides move by the same constant, so the order is kept. `y > 0.0` compares with one unit of an unnamed quantity: rejected. |
| `floor`, `ceil`, `round`, `trunc` | kept | rounds the logarithm in its own unit, as for any unit. |
| `exp(y)` with `log(u)`, `2.0^y` with `log2(u)`, `10.0^y` with `log10(u)` | `u` | b^(log_b x) = x. A mismatched base is rejected, with the matching exponential and `.to` in the menu. |
| `.to` between log units of one vector | adds log_b(c) and multiplies by ln b / ln b' | log10(km) to log10(m) adds 3; log(km) to log(m) adds ln 1000; log10(m) to log(m) multiplies by ln 10. On `rat` a term that is not rational is rejected. |
| everything else: `y1 * y2`, `y * (3 with units("m"))`, `abs`, `sqrt`, `^`, `log(y)`, a unit variable standing for one | rejected | the result does not move by a constant fixed by the units (`abs` changes sign at a point that moves with the unit). |

Linearity and associativity [C by the identity above]: the map from a log unit to its vector is a group homomorphism from (log units of base b, +) to (ℚⁿ, +), so `+` on log units is associative and commutative and inference stays linear over ℚ with one more coordinate, the base, which unifies by equality. A log unit never multiplies with an ordinary unit, so the two groups never mix in one product and the existing unification is unchanged.

The rule most likely to be questioned: **a unit variable never stands for a logarithmic unit**. `twice(x) = 2.0 * x` has the unit `u → u` for ordinary units (scaling keeps a unit) but would need `log(u) → log(u^2)` for a log unit, so a generic definition's unit signature would be wrong if the variable could be a log unit (Kennedy's parametricity). A definition takes a log value only where its parameter's type writes a log unit.

### Kinds and point units

A log unit has no kind and is never a point unit: the log of a temperature reading in °C changes with the zero of the scale, not by a constant, and a kind would have no rule that keeps it through `+`. So `log(p.to("1"))` for a percentage and `log(m.to("N m"))` for a torque, written in Kinds rule 4.

### The decibel, the neper and pH

| Option | Score | Reason |
|---|---|---|
| Leave `dB`, `Np`, `B` out of the prelude; write the log of a ratio to a named reference | 9 | SI Table 8 note (m): these express "specified logarithmic ratio quantities", and "it is important that the quantity be specified, and that any reference value used be specified". A unit word alone cannot say which quantity (power or field, factor 10 or 20) or which reference. |
| `dB` as a unit word | 3 | `3 dB` of power and of field amplitude differ by a factor of two; the unit would carry no reference. |
| `dB` as `10·log10(1)` scaled `1` | 4 | Correct only for power ratios; field quantities need 20; the label would mislead. |

So dBm is `10.0 * log10(p / (1.0 with units("mW")))`, a number in `1`, and pH is `-log10(c / (1.0 with units("mol/L")))`. Both are the SI's own definitions (`m = 10 lg(X/X0)`). A program that wants the log unit instead writes `log10(p)`, in `log10(W)` when `p` is in `W`.

### Display

`log(m^2)`, `log10(L/mol)`: the base word around the base form of the unit; `log(1)` prints `1`. `UnitText` accepts `log(…)`, `log2(…)` and `log10(…)` around a unit with no kind, as a whole text, never a factor (`"log(m) s"` is rejected, as are `"log(N m #torque)"` and `"ln(m)"`).

## Full examples

The two examples of this study, with each line's value or rejection, are the fences DESIGN.md [sec:facets] 7 (the logarithmic algebra, "Logarithmic units", `len = 5.0 with units("m");`) and DESIGN.md [sec:facets] 8 (`without` and casts, `n = 1200 with units("m");`); this repository keeps no copy of them (item SPEC-no-verbatim). The values were computed with IEEE double arithmetic [C: perl `log`, `exp`, `POSIX::log10` on this machine, 2026-11-11].

The author's own example, `log(5 with units("m"))`, gives 1.6094379124341003 with units `log(m)`: the bare literal takes `f64` from the argument of `log` (author, 2026-11-09).

Each `✗` line of those fences is a variant of `zed/fences/variants.txt`, built from the spec at test time (`log-unit-product`, `log-unit-compared-with-number`, `exponential-base-differs`, `removed-fact-not-carried`, `removed-fact-not-removable`), pinned in `l01_29_diagnostics::variants` to the diagnostic zedc gives today (the first `with units("m")` is not compiled yet). Plan row FACET-ops-tests turns the fences and the six new rows of sec:diagnostics into tests once L12.2k is done.

## The new rejection rows (sec:diagnostics)

| Row | Example | Menu |
|---|---|---|
| Fact written on a value that carries a different one | `(d / t) with units("km/h")` with `d` in `m`, `t` in `s`; `(d / d) with units("%")` | `(d / t).to("km/h")`; the fact corrected to `with units("m/s")`; `without` before the second fact |
| Fact removed that the value does not carry | `n without units("km")` with `n` in `m` | `n without units("m")`; `n.to("km") without units("km")` |
| Fact removed from a facet that does not allow it | `userInput without taint(#user)`; `x without bits(8)` | each named sanitizer in scope; for a representation fact, a cast to a type written without it; deleting `without` |
| Unit that an operation does not take | `bitAnd(n, mask)` with `n` in `m`; `exp(t)` with `t` in `s`; `log(p)` with `p` in `%` | `bitAnd(n without units("m"), mask)`; `exp(t / (1.0 with units("s")))`; `log(p.to("1"))` |
| Logarithmic unit in an operation that would change with the unit | `y * y`, `abs(y)`, `y > 0.0`, `twice(y)` with `y` in `log(m)` | `log(len / (1.0 with units("m")))`, in `1`; `y > log(1.0 with units("m"))`; a compile-time scale |
| Exponential whose base differs from the logarithm's | `exp(far)` with `far` in `log10(m)` | `10.0^far`; `exp(far.to("log(m)"))` |

## What was decided without the author, and where it could be wrong

- The string cast writes the unit (score 8 against 6 for rejecting); a program that writes CSV must write `without`. If the author prefers rejection, only the cast rule and one fence line change.
- `removable` is true for `names` and `order` as well as `units`. The author's decision named units only.
- A unit variable never stands for a log unit. This is the claim most likely to be challenged: it makes a generic `twice` unusable on log values, which is sound but may surprise a reader who expects `twice(log(len))` to work.
- `fma`, `hypot`, `gcd`, `clamp`, the shifts and the bit functions got unit rules here for the first time; the rules follow from `+`, `*` and "a pattern of bits has no unit", and each has a test in plan row L12.2j.
