> [!NOTE]
> **Zed is still under construction and is not yet ready for use, but it is coming soon.**
> Releases will be announced at [x.com/zedlang](https://x.com/zedlang). This page describes the language as it will be when finished.

<p align="center">
  <img src="docs/assets/banner.svg" alt="Zed" width="512">
</p>

Zed is a dataflow programming language. A program is a set of definitions, each value is defined once in terms of the values it depends on, and the compiler orders the computation from that graph of dependencies. From the same graph, the compiler:

- runs code in parallel, with no threads or locks in the source, and gives the same result bit for bit on any number of cores;
- frees memory without a garbage collector, and often never allocates intermediate collections at all;
- recomputes only what a changed input affects;
- rejects whole classes of runtime error at compile time, including null dereference, unhandled failure, out-of-bounds indexing and data races.

Its central data structure is the multi-level map, and the same code works on maps held in memory, in files or in a database.

- [A worked example](#a-worked-example): sales by region, day and product, one step at a time
- [A complete program](#a-complete-program): reading a file and printing a result
- [The basics](#the-basics): bindings, functions, numbers, strings, structs, unions, generics, modules
- [Failure is a value](#failure-is-a-value)
- [Collections](#collections): maps, grouping, remapping, reducing, pushing, joins, chunks, matrices
- [Time and repetition](#time-and-repetition): recurrences, loops, methods, running only what's needed
- [The outside world](#the-outside-world): ports, retries, databases, incremental updates
- [Checks at compile time](#checks-at-compile-time): ranges, units, taint, cost
- [Code that runs at build time](#code-that-runs-at-build-time): partial evaluation, reflection, grammars, symbolic math
- [Tests, laws and proofs](#tests-laws-and-proofs)
- [Under the hood](#under-the-hood): error messages, C, memory, parallelism, targets

## A worked example

This example follows one small data set from raw sales records to totals, a running sum, a stock count and a check of physical units. Each step shows its code, explains what is new in it, and shows the value it computes. Boxes like the ones below define each word and form the first time it appears.

### Step 1: the data

A shop records how many of each product it sold, per region and per day, and keeps its prices in a second table.

```zed
// region -> day -> sku -> quantity sold
sales: Utf8String ->? [Utf8String ->? int];

// sku -> price in dollars
prices: Utf8String ->? int;
```

> [!NOTE]
> **`name: T;`** declares a name and its type without giving the value. Here the values come from outside the code shown, so `sales` and `prices` are this example's inputs. Text from `//` to the end of the line is a comment.

The types say what shape the data has.

> [!NOTE]
> **`K ->? V`** is the type of a *map* from keys of type `K` to values of type `V` that may lack some keys. A map sends each *key* to a *value*, and a key with its value is an *entry*. `K -> V`, with no `?`, has a value at every key of `K`.
>
> **`[T]`** is an array of `T`: a map whose keys are `0`, `1`, `2` and so on.
>
> **`int`** is a mathematical integer, which can't overflow, and **`Utf8String`** is text in UTF-8. A *sku* is a product code.

So `sales` is a map from each region to an array with one entry per day, and each day maps a sku to the quantity sold. A map whose values are maps is a multi-level map, Zed's basic structure for data.

> [!NOTE]
> **Level**: one layer of keys in a multi-level map. `sales` has three levels: region, day and sku.
>
> **Keypath**: the chain of keys that leads to one value, such as `("East", 0, "pen")`. One rule holds for every map in Zed: a keypath leads to exactly one value.

Here are the two inputs the rest of the example uses.

> [!TIP]
> **How this page shows data.** Each table has a bold line above it naming the value it shows. A line starting with `input:` names a value the code reads but doesn't show. Each column but the last is one level of keys, and the last column holds the values. A key is printed once and covers every row beside it, and rows are listed in key order. Where a table has several columns after its keys, they are parts of one value. The tables are not Zed code.

**input: `sales`**

<table>
<tr><th><code>region</code></th><th><code>day</code></th><th><code>sku</code></th><th><code>quantity</code></th></tr>
<tr><td rowspan="3"><code>East</code></td><td rowspan="2"><code>0</code></td><td><code>ink</code></td><td><code>2</code></td></tr>
<tr><td><code>pen</code></td><td><code>5</code></td></tr>
<tr><td><code>1</code></td><td><code>pen</code></td><td><code>3</code></td></tr>
<tr><td rowspan="3"><code>West</code></td><td rowspan="2"><code>0</code></td><td><code>pad</code></td><td><code>1</code></td></tr>
<tr><td><code>pen</code></td><td><code>4</code></td></tr>
<tr><td><code>1</code></td><td><code>ink</code></td><td><code>6</code></td></tr>
</table>

**input: `prices`**

<table>
<tr><th><code>sku</code></th><th><code>price</code></th></tr>
<tr><td><code>ink</code></td><td><code>7</code></td></tr>
<tr><td><code>pen</code></td><td><code>2</code></td></tr>
</table>

The price list has no entry for `pad`. That gap comes back in step 3.

### Step 2: looking up a keypath

```zed
northOrZero = northPens else 0;
northPens = sales["North"][0]["pen"];
eastPens = sales["East"][0]["pen"];
```

> [!NOTE]
> **`name = value;`** is a *binding*: it gives a name to a value, once. A name can't be reassigned.
>
> **`m[k]`** looks up the key `k` in the map `m`. Each `[k]` goes one level down, so `sales["East"][0]["pen"]` follows the keypath `("East", 0, "pen")`.

The first line uses `northPens` before the line that defines it. That is fine: definitions can come in any order, and the compiler computes each value from the values it depends on. Because each name has one value, you never have to ask what it holds at some point in the program.

There is no region `"North"`, so that lookup finds nothing and gives an *atom*.

> [!NOTE]
> **`#name`** is an *atom*: a value that is just a name, like an enum value, that needs no declaration. Writing `#tooYoung` anywhere is enough. A lookup that finds no entry gives the atom **`#notFound`**.
>
> **`A | B`** is a *union*, the type of a value that is either an `A` or a `B`. `northPens` has the type `int | #notFound`, and the compiler works that out without being told.

Zed uses atoms to report failure. A *failure* is an atom in a value's type that says an operation didn't give a result.

> [!TIP]
> Where another language would throw an exception or return null, a Zed operation returns an atom, and its type says so until the caller handles it. In Python, `sales["North"]` raises `KeyError`, and nothing in the code warns you. When you want a fixed set of names, as with an enum, you give the union a name with `type`: `type Light = #red | #amber | #green;`.

`else` is one way to handle a failure.

> [!NOTE]
> **`x else d`** gives `x`, or `d` in place of a failure. `x else #a -> d` replaces only the atom `#a`.

**`eastPens`, `northPens` and `northOrZero`**

<table>
<tr><th><code>eastPens</code></th><th><code>northPens</code></th><th><code>northOrZero</code></th></tr>
<tr><td><code>5</code></td><td><code>#notFound</code></td><td><code>0</code></td></tr>
</table>

### Step 3: revenue per sale

The revenue of each entry is its quantity times its price.

```zed
revenue = sales as (region -> day -> sku -> q) into (region -> day -> sku -> q * prices[sku]);
```

> [!NOTE]
> **`m as (pattern) into (pattern)`** is a *remap*, which reshapes a map. A *pattern* names the shape of a value. The `as` pattern gives a name to each level of `m` and to its value, and the `into` pattern draws the shape of the result with those names, ending in an expression for each new value. Here the shape stays the same, and each quantity `q` becomes `q * prices[sku]`.

**`revenue`**

<table>
<tr><th><code>region</code></th><th><code>day</code></th><th><code>sku</code></th><th><code>revenue</code></th></tr>
<tr><td rowspan="3"><code>East</code></td><td rowspan="2"><code>0</code></td><td><code>ink</code></td><td><code>14</code></td></tr>
<tr><td><code>pen</code></td><td><code>10</code></td></tr>
<tr><td><code>1</code></td><td><code>pen</code></td><td><code>6</code></td></tr>
<tr><td rowspan="3"><code>West</code></td><td rowspan="2"><code>0</code></td><td><code>pad</code></td><td><code>#notFound</code></td></tr>
<tr><td><code>pen</code></td><td><code>8</code></td></tr>
<tr><td><code>1</code></td><td><code>ink</code></td><td><code>42</code></td></tr>
</table>

`prices["pad"]` is `#notFound`, and so is `1 * #notFound`: a failure passes through arithmetic unchanged. When two different failures meet, the result keeps both: if `#invalid` stands for a number that failed to parse, `(1 + #notFound) + #invalid` is `#errs({#invalid, #notFound})`, the set of the two, and `((1 + #notFound) + #invalid) else 0` is `0`, as for a single failure. It stays in the map at its own keypath, next to the good values, so one bad record doesn't stop the rest of the computation. The type of `revenue`'s values, `int | #notFound`, says that some may be failures.

> [!TIP]
> Elsewhere this remap is three nested loops that fill a new nested dictionary. A remap can also move levels: `matrix as (r -> c -> v) into (c -> r -> v)` transposes a matrix, where other languages set `out[c][r] = matrix[r][c]` in two nested loops. [Remapping](#remapping) below compares remaps with spreadsheet pivot tables.

### Step 4: sales with no price

To list the entries that have no price, flatten `revenue` to one level and keep the failures.

```zed
flat = revenue as (region -> day -> sku -> r) into ((region, day, sku) -> r);
unpriced = flat.where(r -> r is not int);
```

> [!NOTE]
> **`(a, b, c)`** is a *tuple*, a fixed number of values that may have different types. As a key, it packs three levels into one.
>
> **`x -> e`** is an unnamed function (a lambda) that gives `e` for the argument `x`.
>
> **`m.where(f)`** keeps the entries whose value passes the test `f`, with their keys. A call with a dot passes the value before the dot as the first argument, so `m.where(f)` is `where(m, f)`.
>
> **`x is T`** tests whether `x` has the type `T`, and **`x is not T`** tests that it doesn't.

**`flat`**

<table>
<tr><th><code>(region, day, sku)</code></th><th><code>r</code></th></tr>
<tr><td><code>("East", 0, "ink")</code></td><td><code>14</code></td></tr>
<tr><td><code>("East", 0, "pen")</code></td><td><code>10</code></td></tr>
<tr><td><code>("East", 1, "pen")</code></td><td><code>6</code></td></tr>
<tr><td><code>("West", 0, "pad")</code></td><td><code>#notFound</code></td></tr>
<tr><td><code>("West", 0, "pen")</code></td><td><code>8</code></td></tr>
<tr><td><code>("West", 1, "ink")</code></td><td><code>42</code></td></tr>
</table>

**`unpriced`**

<table>
<tr><th><code>(region, day, sku)</code></th><th><code>r</code></th></tr>
<tr><td><code>("West", 0, "pad")</code></td><td><code>#notFound</code></td></tr>
</table>

The failure keeps its keypath, so `unpriced` says exactly which record lacks a price.

### Step 5: daily totals

The daily total of a region adds up the revenue of its skus. The obvious first try leaves the `sku` level out of the `into` pattern:

```zed
// daily = revenue as (region -> day -> sku -> r) into (region -> day -> r);   // ✗ Collision: two skus land on one keypath
```

> [!TIP]
> A line commented out and marked `// ✗` is one the compiler rejects. The words after the ✗, up to the colon, name the kind of error, as the compiler's message names it; the text after the colon gives the reason.

This line keeps each row of `revenue` but removes its sku. Here is the result it asks for, with ✗ next to each value that shares its keypath with another:

**`revenue` with the `sku` level removed**

<table>
<tr><th><code>region</code></th><th><code>day</code></th><th><code>r</code></th><th>sku it came from</th></tr>
<tr><td rowspan="3"><code>East</code></td><td rowspan="2"><code>0</code></td><td><code>14</code> ✗</td><td><code>ink</code></td></tr>
<tr><td><code>10</code> ✗</td><td><code>pen</code></td></tr>
<tr><td><code>1</code></td><td><code>6</code></td><td><code>pen</code></td></tr>
<tr><td rowspan="3"><code>West</code></td><td rowspan="2"><code>0</code></td><td><code>#notFound</code> ✗</td><td><code>pad</code></td></tr>
<tr><td><code>8</code> ✗</td><td><code>pen</code></td></tr>
<tr><td><code>1</code></td><td><code>42</code></td><td><code>ink</code></td></tr>
</table>

The keypath `("East", 0)` would lead to both 14 and 10, and `("West", 0)` to both `#notFound` and 8. A keypath leads to exactly one value (step 1), so this is not a map, and the compiler rejects the line:

```text
error: this remap would map one key to many values
  the `(region, day, sku)` keypaths collapse onto `(region, day)`, but their values survive.
  drop the values too:         into (region -> day -> sku -> _)
  or keep the inner key:       into (region -> day -> sku -> r)
  or say how the values merge: into (region -> day -> sku >< op -> r)
```

> [!IMPORTANT]
> **A remap never merges values unless you say how.** The compiler reads this from the pattern, not the data: `(region -> day -> r)` drops a level and keeps the values beneath it, so the line is rejected even for an input with one sku per day.

Other tools meet the same collision later, or not at all:

<table>
<tr><th>The same step written in</th><th>What happens at <code>("East", 0)</code></th></tr>
<tr><td>Python, <code>daily[(region, day)] = r</code> in a loop</td><td>the value is <code>10</code>, ink's <code>14</code> is lost, and nothing reports it</td></tr>
<tr><td>SQL, an insert into a table keyed by <code>(region, day)</code></td><td>a duplicate-key error while the program runs</td></tr>
<tr><td>Zed</td><td>the error above, at compile time</td></tr>
</table>

The error lists three repairs. Two of them use forms not seen yet.

> [!NOTE]
> **`_`** in the value position of a pattern drops the values.
>
> **`k >< op`** in an `into` pattern collapses the level `k`, merging the values that land on one keypath with the operator `op`. **`(+)`** is the operator `+` used as a function.

**What each repair gives at `("East", 0)`**

<table>
<tr><th>Repair</th><th><code>into</code> pattern</th><th>Value at <code>("East", 0)</code></th></tr>
<tr><td>drop the values</td><td><code>(region -> day -> sku -> _)</code></td><td>the skus <code>ink</code> and <code>pen</code>, with no revenue</td></tr>
<tr><td>keep the <code>sku</code> level</td><td><code>(region -> day -> sku -> r)</code></td><td><code>ink</code> → <code>14</code>, <code>pen</code> → <code>10</code>, as in <code>revenue</code></td></tr>
<tr><td>merge with <code>+</code></td><td><code>(region -> day -> sku >< (+) -> r)</code></td><td><code>24</code></td></tr>
</table>

Only the third gives a daily total.

### Step 6: adding values that may be failures

Merging with `+` gives the right total at `("East", 0)`:

```zed
dailyAll = revenue as (region -> day -> sku -> r) into (region -> day -> sku >< (+) -> r);
```

At `("West", 0)`, `+` would have to add these two values:

**`revenue["West"][0]`**

<table>
<tr><th><code>sku</code></th><th><code>r</code></th></tr>
<tr><td><code>pad</code></td><td><code>#notFound</code> ✗</td></tr>
<tr><td><code>pen</code></td><td><code>8</code></td></tr>
</table>

`+` is defined on integers. Adding only the integers would give `8`, which looks like a total and hides that pad has no price. So a merge runs `+` only when none of the values it merges is a failure. Otherwise `+` does not run, and the result is the failures. The type of `dailyAll`'s values is `int | #notFound`, so the code that reads them has to deal with the failure:

**`dailyAll`**

<table>
<tr><th><code>region</code></th><th><code>day</code></th><th><code>total</code></th></tr>
<tr><td rowspan="2"><code>East</code></td><td><code>0</code></td><td><code>24</code></td></tr>
<tr><td><code>1</code></td><td><code>6</code></td></tr>
<tr><td rowspan="2"><code>West</code></td><td><code>0</code></td><td><code>#notFound</code></td></tr>
<tr><td><code>1</code></td><td><code>42</code></td></tr>
</table>

The failures are kept as a set. The compiler may add one day's values in any order, splitting them across cores. Suppose a day held two different failures, `#notFound` and `#invalid` (a number that failed to parse), and a merge kept the first failure it met. The result would depend on the order:

<table>
<tr><th>Order of the additions</th><th>Result if the first failure wins</th><th>Zed's result</th></tr>
<tr><td><code>(#notFound + 8) + #invalid</code></td><td><code>#notFound</code></td><td><code>#errs({#invalid, #notFound})</code></td></tr>
<tr><td><code>(#invalid + 8) + #notFound</code></td><td><code>#invalid</code></td><td><code>#errs({#invalid, #notFound})</code></td></tr>
</table>

So the same program could give different totals on one core and on eight. Zed keeps both failures, as in step 3, and keeps them in a set rather than a list, because a list would record the order the additions ran in and the two rows would again differ.

> [!IMPORTANT]
> **A merge gives its total only when every value is one its operator is defined for, and otherwise gives the failures.** Nothing is dropped or replaced unless the code says so. To get a total anyway, say what the failures mean: replace them with `else`, filter them out with `where`, or keep them apart, as step 4 did.

This version counts an unpriced sale as zero revenue:

```zed
daily = revenue as (region -> day -> sku -> r) into (region -> day -> sku >< (+) -> (r else 0));
```

`unpriced` from step 4 still lists the pad sale, so the zero hides nothing.

**`daily` before summing over `sku`**

<table>
<tr><th><code>region</code></th><th><code>day</code></th><th><code>sku</code></th><th><code>r else 0</code></th></tr>
<tr><td rowspan="3"><code>East</code></td><td rowspan="2"><code>0</code></td><td><code>ink</code></td><td><code>14</code></td></tr>
<tr><td><code>pen</code></td><td><code>10</code></td></tr>
<tr><td><code>1</code></td><td><code>pen</code></td><td><code>6</code></td></tr>
<tr><td rowspan="3"><code>West</code></td><td rowspan="2"><code>0</code></td><td><code>pad</code></td><td><code>0</code></td></tr>
<tr><td><code>pen</code></td><td><code>8</code></td></tr>
<tr><td><code>1</code></td><td><code>ink</code></td><td><code>42</code></td></tr>
</table>

**`daily`**

<table>
<tr><th><code>region</code></th><th><code>day</code></th><th><code>total</code></th></tr>
<tr><td rowspan="2"><code>East</code></td><td><code>0</code></td><td><code>24</code></td></tr>
<tr><td><code>1</code></td><td><code>6</code></td></tr>
<tr><td rowspan="2"><code>West</code></td><td><code>0</code></td><td><code>8</code></td></tr>
<tr><td><code>1</code></td><td><code>42</code></td></tr>
</table>

### Step 7: totals per region

```zed
regionTotals = daily >< (+);
```

> [!NOTE]
> **`m >< op`** *reduces* the innermost level of `m`: it merges that level's values into one with the operator `op`. On `daily`, the innermost level is `day`, so the result has one total per region.

**`regionTotals`**

<table>
<tr><th><code>region</code></th><th><code>total</code></th></tr>
<tr><td><code>East</code></td><td><code>30</code></td></tr>
<tr><td><code>West</code></td><td><code>50</code></td></tr>
</table>

> [!TIP]
> This is `reduce` or `fold` in other languages, but you give no direction, because the work can be split across cores. So the reducer must be associative, and ideally also commutative.

Each property allows a different split of the work. With four values `a`, `b`, `c` and `d`:

<table>
<tr><th>Property of <code>op</code></th><th>Law</th><th>What the compiler may do</th></tr>
<tr><td>associative</td><td><code>(a op b) op c == a op (b op c)</code></td><td>add <code>a + b</code> on one core and <code>c + d</code> on another, then add the two results</td></tr>
<tr><td>commutative</td><td><code>a op b == b op a</code></td><td>also combine the values in whatever order they arrive, with no sort first</td></tr>
</table>

`+` on integers has both properties. `-` has neither: `(5 - 3) - 1` is 1, but `5 - (3 - 1)` is 3, so `daily >< (-)` is rejected. Joining strings is associative but not commutative, so its reduction keeps the order of the level. Floating-point values have their own rule, in [Reducing](#reducing) below.

### Step 8: units sold per product

So far each value was computed from where its data comes from. Sometimes it's clearer to say where each value goes. This step counts the units sold of each sku by sending each sale's quantity to its sku.

```zed
lines = sales as (region -> day -> sku -> q) into ((region, day, sku) -> { sku:, q: });

sold: Utf8String ->? int with reducer((+));
for line in lines { sold[line.sku] <- line.q; };
```

> [!NOTE]
> **`{ sku: s, q: n }`** is a *struct* value: a record of named *fields*. `{ sku:, q: }` is short for `{ sku: sku, q: q }`, and `line.sku` reads the field `sku`.
>
> **`for x in m { ... }`** runs its body once for each entry of `m`, with `x` bound to the entry's value.

`lines` is `sales` flattened as in step 4, with each value a record of the sku and the quantity. The declaration of `sold` has no value: `sold` is filled by pushes.

> [!NOTE]
> **`name[k] <- v`** *pushes* the value `v` to the key `k` of the map `name`. **`with reducer(op)`** in the declaration says how values pushed to one key merge, here by adding them.

**`lines`**

<table>
<tr><th><code>(region, day, sku)</code></th><th><code>line</code></th></tr>
<tr><td><code>("East", 0, "ink")</code></td><td><code>{ sku: "ink", q: 2 }</code></td></tr>
<tr><td><code>("East", 0, "pen")</code></td><td><code>{ sku: "pen", q: 5 }</code></td></tr>
<tr><td><code>("East", 1, "pen")</code></td><td><code>{ sku: "pen", q: 3 }</code></td></tr>
<tr><td><code>("West", 0, "pad")</code></td><td><code>{ sku: "pad", q: 1 }</code></td></tr>
<tr><td><code>("West", 0, "pen")</code></td><td><code>{ sku: "pen", q: 4 }</code></td></tr>
<tr><td><code>("West", 1, "ink")</code></td><td><code>{ sku: "ink", q: 6 }</code></td></tr>
</table>

**`sold`**

<table>
<tr><th><code>sku</code></th><th><code>units</code></th></tr>
<tr><td><code>ink</code></td><td><code>8</code></td></tr>
<tr><td><code>pad</code></td><td><code>1</code></td></tr>
<tr><td><code>pen</code></td><td><code>12</code></td></tr>
</table>

> [!TIP]
> This looks like `sold[k] += q` on a dictionary in Python, but nothing is read back or overwritten. `sold` has one value, all its pushes merged per key, so pushes can come from many places in a program and from many cores at once, with no locks.

A push and the matching read compile to the same thing: the same table could be computed by a remap that moves `sku` to the top level and sums over region and day. Write whichever reads more clearly.

### Step 9: a running total

East's daily revenue as an array, and its running total:

```zed
east = daily["East"] else [];
running[i] = running[i-1] + east[i] with running[-1] = 0;
```

> [!NOTE]
> **`x[i] = e with x[-1] = start;`** is a *recurrence*: it defines every entry of the array `x` by one equation, which may read earlier entries. The `with` part gives the *boundary* value, the one a read just below the first index finds. `running[-1]` is not an entry of the result.

`daily["East"]` may be `#notFound`, so `else []` gives an empty array in its place, and `east` is an array of `int`.

**`east`**

<table>
<tr><th><code>day</code></th><th><code>total</code></th></tr>
<tr><td><code>0</code></td><td><code>24</code></td></tr>
<tr><td><code>1</code></td><td><code>6</code></td></tr>
</table>

**`running`**

<table>
<tr><th><code>i</code></th><th><code>running</code></th></tr>
<tr><td><code>0</code></td><td><code>24</code></td></tr>
<tr><td><code>1</code></td><td><code>30</code></td></tr>
</table>

> [!TIP]
> Elsewhere this is a `for` loop that fills an array in order. Here it's a statement about every entry, and the compiler reads the dependencies and picks the order. [Recurrences](#recurrences) below shows what else that allows, such as running a scan like this one on many cores.

### Step 10: the change from the day before

A loop describes one step, and the loop as a whole is a value.

```zed
trend = loop t {
  while t < east::len;
  prev' = east[t] with prev = 0;
  change' = east[t] - prev with change = 0;
};
```

> [!NOTE]
> **`loop t { ... }`** repeats its body, with `t` as the step counter, counting from 0. **`while c;`** is tested before each step and ends the loop when `c` is false, and **`until c;`** is tested after each step and ends it when `c` is true. **`x::len`** is the number of entries in `x`. The loop is a value: `trend.prev` is the final `prev`, and `trend::len` is the number of steps.
>
> **`x' = e`** gives `x`'s value in the next step. In the step, `x` is the value from the previous step. **`with x = start`** gives the value before the first step.

**`trend`, one row per step**

<table>
<tr><th><code>t</code></th><th><code>prev</code></th><th><code>change</code></th></tr>
<tr><td><code>0</code></td><td><code>24</code></td><td><code>24</code></td></tr>
<tr><td><code>1</code></td><td><code>6</code></td><td><code>-18</code></td></tr>
</table>

**`trend.prev`, `trend.change` and `trend::len`**

<table>
<tr><th><code>trend.prev</code></th><th><code>trend.change</code></th><th><code>trend::len</code></th></tr>
<tr><td><code>6</code></td><td><code>-18</code></td><td><code>2</code></td></tr>
</table>

> [!TIP]
> In Python the body would be `prev, change = x, x - prev`, and in C it needs a temporary. In Zed, writing `prev'` doesn't change `prev`, so the `change'` line still reads the previous day's value, and the two lines could be swapped. Each step writes each variable once.

### Step 11: pens left on the shelf

The East store starts the period with 20 pens on its shelf. This step follows the count as the pens sell.

```zed
eastPenDays = (sales["East"] else []).map(day -> day["pen"] else 0);

struct Shelf { pens: int }

Shelf.sell(positional n: int) -> int {
  pens' = pens - n;
  return pens;
}

stock = loop t {
  while t < eastPenDays::len;
  mutable s = Shelf(pens: 20);
  before = s*.sell(eastPenDays[t]);
};
```

> [!NOTE]
> **`m.map(f)`** replaces each value `v` with `f(v)` and keeps the keys. Here each day's map of skus becomes the number of pens sold that day.
>
> **`struct Name { field: T }`** declares a struct type, and **`Name(field: value)`** builds one.

A method is a function you call on a struct with a dot.

> [!NOTE]
> **`Name.method(...) -> T { ... }`** defines a method of the struct `Name`, whose result has the type `T`. In the body, the struct's fields are in scope by name, and **`return e;`** ends the body with the result `e`. A parameter marked **`positional`** is passed by position, as in `s.sell(3)`. Other parameters are passed by name, as in `f(x: 1)`.
>
> A method can write a field with a `'`, such as `pens' = pens - n`, which gives the field's value in the struct's next version. The call returns that new struct along with its result and leaves the old one alone.

In a loop, `*.` makes the new struct the value of `s` in the next step.

> [!NOTE]
> **`mutable x = e;`** declares a loop variable that starts as `e` and keeps its value in any step that doesn't write `x'`. **`x*.method()`** calls the method and also makes the struct it returns the value of `x` in the next step: `before = s*.sell(3);` is short for `s', before = s.sell(3);`, where **`a, b = e;`** binds each name to one part of a result that has several parts.

So each step of `stock` sells one day's pens, records the count before the sale in `before`, and hands the shelf with its new count to the next step.

> [!IMPORTANT]
> **No call changes a value you hold unless the code shows a `*`.** `s.sell(3);` alone is rejected, because its result would be thrown away, and `s*.sell(3)` on a value bound with `=` is rejected, because there is no next step to write. So you can find every change of state by reading.

**`eastPenDays`**

<table>
<tr><th><code>day</code></th><th><code>pens</code></th></tr>
<tr><td><code>0</code></td><td><code>5</code></td></tr>
<tr><td><code>1</code></td><td><code>3</code></td></tr>
</table>

**`stock`, one row per step**

<table>
<tr><th><code>t</code></th><th><code>before</code></th><th><code>s.pens</code> in the next step</th></tr>
<tr><td><code>0</code></td><td><code>20</code></td><td><code>15</code></td></tr>
<tr><td><code>1</code></td><td><code>15</code></td><td><code>12</code></td></tr>
</table>

**`stock.s.pens` and `stock::len`**

<table>
<tr><th><code>stock.s.pens</code></th><th><code>stock::len</code></th></tr>
<tr><td><code>12</code></td><td><code>2</code></td></tr>
</table>

> [!TIP]
> `s*.sell(n)` reads like a mutating method call in Java or Python, with two differences. The rest of the step still reads the old `s`. And a step can write `s'` only once, so two calls in one step have to be one chain: `a, b = s*.sell(1).sell(2);`.

### Step 12: the mass of the shipment

The pens sold go out in one crate. A unit on each number lets the compiler check the arithmetic.

```zed
penMass = 20 with units("g");          // one pen
crateMass = 1 with units("kg");        // the crate they ship in
shipped = (sold["pen"] else 0) * penMass;
// load = shipped + crateMass;         // ✗ Units that differ where an operation requires equal ones: g + kg
load = shipped + crateMass * (1000 with units("g/kg"));
```

> [!NOTE]
> **`e with units("...")`** attaches a physical unit to a number. A unit is a *facet*: an extra fact about a value that the compiler tracks through every operation. Units multiply under `*`, so `shipped` is in grams, and must match under `+`. `sold["pen"] else 0` has parentheses because `else` applies to everything to its left.

The commented-out line adds grams to kilograms.

> [!IMPORTANT]
> **Adding values with different units is rejected.** `g` and `kg` are different units, and the compiler never converts between them on its own. A conversion factor, here `1000` grams per kilogram, makes the conversion visible in the code.

**`penMass`, `crateMass`, `shipped` and `load`**

<table>
<tr><th><code>penMass</code></th><th><code>crateMass</code></th><th><code>shipped</code></th><th><code>load</code></th></tr>
<tr><td><code>20 g</code></td><td><code>1 kg</code></td><td><code>240 g</code></td><td><code>1240 g</code></td></tr>
</table>

> [!TIP]
> In other languages a unit usually takes a wrapper type such as `Grams`, with its arithmetic written by hand. A facet leaves the value an `int`, and the compiler follows the unit through each operation, at no cost when the program runs.

### Step 13: the whole calculation

Here are the definitions behind `regionTotals`, written with the result first:

```zed
regionTotals = daily >< (+);
daily = revenue as (region -> day -> sku -> r) into (region -> day -> sku >< (+) -> (r else 0));
revenue = sales as (region -> day -> sku -> q) into (region -> day -> sku -> q * prices[sku]);

sales: Utf8String ->? [Utf8String ->? int];
prices: Utf8String ->? int;
```

**`regionTotals`**

<table>
<tr><th><code>region</code></th><th><code>total</code></th></tr>
<tr><td><code>East</code></td><td><code>30</code></td></tr>
<tr><td><code>West</code></td><td><code>50</code></td></tr>
</table>

The order of the lines doesn't matter, only what depends on what, so you can write a calculation top-down, from the result to its parts, and the compiler reads the dependency graph straight from the text. The same graph lets it run the two regions, or the days within them, on different cores, and skip whatever no result needs: if a program reads only `regionTotals`, then `unpriced`, `sold` and the rest of the steps above are never computed.

## A complete program

The example above reads values it was given. A complete program also needs input and output. This one reads a file, counts each word, and prints the counts, most common first.

```zed
main(fs: Files) -> (stdout: Lines) {
  text = fs["input.txt"] else "";
  counts = text.split(" ").group(w -> w.lower).count;
  lines = counts as (w -> n) into (desc n -> w -> "${w}: ${n}");
  stdout <- lines.rank;
}
```

> [!NOTE]
> **`main(input: T) -> (output: U) { ... }`** is a program's entry point. Its parameters and results are *ports*: declared channels to the outside world, such as files, sockets, clocks and databases. A port is the only way a program reaches the outside world.
>
> **`Files`** is a port that maps each path to the text of that file, so `fs["input.txt"]` reads one file, and **`Lines`** is a port that takes lines of text, so `stdout` prints them. **`"text"`** is a string literal, a `Utf8String`.

Reading a file can fail, and the `else` says what to do when it does: use the empty text. The next line counts the words.

> [!NOTE]
> **`s.split(sep)`** splits the string `s` at each `sep`, giving an array of the pieces. **`w.lower`** is `w` in lowercase.
>
> **`m.group(x -> key)`** adds a level of keys above the existing ones, computed from each value, so entries with the same key land in one group. **`.count`** reduces the innermost level to its number of entries.

The `as ... into ...` line reshapes the counts, and the last line writes them out.

> [!NOTE]
> **`desc k`**, in the key position of an `into` pattern, orders by `k` from high to low and adds a level keyed by *rank*, the position in that order, where equal values share one rank. **`asc k`** orders from low to high.
>
> **`"${e}"`** writes the value of `e` into a string. **`m.rank`** flattens an ordered multi-level map into one array, numbered in that order. **`port <- v`** pushes the value `v` out of a port.

Keeping `w` as a level below `desc n` means that two words with the same count don't collide. These tables show the data after each step, for a file whose whole text is `to be or not to be`.

**`counts` after `.split(" ")`**

<table>
<tr><th><code>i</code></th><th><code>w</code></th></tr>
<tr><td><code>0</code></td><td><code>to</code></td></tr>
<tr><td><code>1</code></td><td><code>be</code></td></tr>
<tr><td><code>2</code></td><td><code>or</code></td></tr>
<tr><td><code>3</code></td><td><code>not</code></td></tr>
<tr><td><code>4</code></td><td><code>to</code></td></tr>
<tr><td><code>5</code></td><td><code>be</code></td></tr>
</table>

**`counts` after `.group(w -> w.lower)`**

<table>
<tr><th><code>w.lower</code></th><th><code>i</code></th><th><code>w</code></th></tr>
<tr><td rowspan="2"><code>be</code></td><td><code>1</code></td><td><code>be</code></td></tr>
<tr><td><code>5</code></td><td><code>be</code></td></tr>
<tr><td><code>not</code></td><td><code>3</code></td><td><code>not</code></td></tr>
<tr><td><code>or</code></td><td><code>2</code></td><td><code>or</code></td></tr>
<tr><td rowspan="2"><code>to</code></td><td><code>0</code></td><td><code>to</code></td></tr>
<tr><td><code>4</code></td><td><code>to</code></td></tr>
</table>

**`counts` after `.count`**

<table>
<tr><th><code>w</code></th><th><code>n</code></th></tr>
<tr><td><code>be</code></td><td><code>2</code></td></tr>
<tr><td><code>not</code></td><td><code>1</code></td></tr>
<tr><td><code>or</code></td><td><code>1</code></td></tr>
<tr><td><code>to</code></td><td><code>2</code></td></tr>
</table>

**`lines`**

<table>
<tr><th><code>rank</code></th><th><code>w</code></th><th><code>line</code></th></tr>
<tr><td rowspan="2"><code>0</code></td><td><code>be</code></td><td><code>be: 2</code></td></tr>
<tr><td><code>to</code></td><td><code>to: 2</code></td></tr>
<tr><td rowspan="2"><code>1</code></td><td><code>not</code></td><td><code>not: 1</code></td></tr>
<tr><td><code>or</code></td><td><code>or: 1</code></td></tr>
</table>

**`lines.rank`**

<table>
<tr><th><code>i</code></th><th><code>line</code></th></tr>
<tr><td><code>0</code></td><td><code>be: 2</code></td></tr>
<tr><td><code>1</code></td><td><code>to: 2</code></td></tr>
<tr><td><code>2</code></td><td><code>not: 1</code></td></tr>
<tr><td><code>3</code></td><td><code>or: 1</code></td></tr>
</table>

The program doesn't mention threads, locks or allocation. The compiler can run the grouping on all your cores, and the output is the same, bit for bit, on one core or on sixty-four. A missing file can't crash the program either: the type of `fs["input.txt"]` says the read can fail, and the `else` says what to do when it does.

Zed exists because many systems already recover a graph of values from ordinary code: spreadsheets, optimizing compilers, Spark, build systems, reactive UI frameworks and out-of-order CPUs. In Zed the graph is the program, so one compiler handles parallel scheduling, memory management, incremental updates and many correctness checks from one structure. This doesn't have to make programs longer: the word-count program above is about as long as the same program in Python.

The rest of this page is a tour of the language, one feature at a time. Each stop opens with a line saying what the feature does and lists its syntax. Most then give an example, explain it and show its inputs and results.

> [!TIP]
> In a **Syntax** line, `x`, `T`, `op`, `pattern`, `fallback`, `#someFailure` and `...` stand for code you would write. Snippets stand alone unless they say otherwise, and a name a snippet doesn't define is an input you can assume.

## The basics

### Bindings

A binding gives a name to a value.

**Syntax:** `name = value;` or `name: type = value;`

> [!NOTE]
> **`name: T = value;`** is a binding with a stated type. **`int[a..=b]`** is an integer in a range, and **`int[a..]`** one with no upper end. The same range forms work as values: **`a..<b`** excludes `b`, **`a..=b`** includes it, and **`a..`** has no upper end.

```zed
total = price * quantity;
price = 12;
quantity = 3;
port: int[1..=65535] = 8080;   // an integer from 1 through 65535, both included
```

```text
total = 36, port = 8080
```

A name is bound once. It can't be reassigned, and it can be used above the line that defines it, as `price` is here: the order of definitions doesn't matter, only what depends on what. Because a name has one value, you never have to ask what it holds at this point in the program, and the compiler can read the dependency graph straight from the text. The type is optional. It can be more exact than in most languages: `port`'s type is a range, and the compiler checks that 8080 lies in it.

### Functions

A function is a definition with parameters, and a call can name its arguments, chain with dots or leave some open.

**Syntax:** `f(positional x, y = default) = expression;` or `f(x) -> type { ... }`

> [!NOTE]
> **`f(x) = expression;`** defines a function whose body is one expression, and **`f(x) -> T { ... }`** one with a block body and a stated result type. A block gives its last expression, unless `return` ends it first. **`y = default`** in a parameter list gives a parameter that can be left out. **`f(x, ...)`** leaves the remaining named parameters open and gives back a function that takes them. **`(T) -> U`** is the type of a function from `T` to `U`. **`if c { a } else { b }`** is a choice between two values, and **`a ++ b`** joins two strings or lists.
>
> The dot call from [Step 4](#step-4-sales-with-no-price) works with any function: `5.double` is `double(5)`.

```zed
double(positional x) = x * 2;

// A { } body gives its last expression, and if gives a value.
clamp(positional v, positional lo, positional hi) -> int {
  if v < lo { lo } else if v > hi { hi } else { v }
}

// Utf8String is UTF-8 text, and ++ joins strings.
greet(positional name: Utf8String, punct = "!") = "Hi, " ++ name ++ punct;

a = 5.double.clamp(0, 8);        // 8
b = greet("Ann", punct: "?");    // "Hi, Ann?"
hi = greet("Ann", ...);          // a function still waiting for punct
```

```text
a = 8, because 5.double is 10 and clamp(0, 8) caps it
b = "Hi, Ann?"
hi(punct: ".") = "Hi, Ann."
hi() = "Hi, Ann!"
```

Parameters are passed by name unless you mark them `positional`, so a call site says what its arguments mean. Because any function can be called with a dot, pipelines read left to right, and adding a step to a pipeline doesn't mean extending a class. Parameter types can usually be left out, and the compiler infers them from how the body uses the parameter. `x * 2` takes any number type, because the literal `2` takes the type of `x`.

### Numbers

Zed has exact integers, rational numbers (fractions of two integers) and floating-point numbers in four formats, `f16`, `bf16`, `f32` and `f64` (16, 16, 32 and 64 bits), and it never converts between them on its own.

**Syntax:** `42`, `1.5`, `0.1f64`, `3r`, `a / b`, `a div b`, `f64(n)`

> [!NOTE]
> **`42`** is an integer literal, which takes whichever number type its use needs, where that type holds it exactly, and is an `int` where nothing else fixes its type. **`3r`** is a `rat`, an exact rational number, a fraction of two integers that is never rounded. A decimal one such as `0.1r` is exactly the decimal it spells, `1r / 10r`, never a rounded binary float.
>
> **`1.5`** is a decimal literal, which takes whichever of `f16`, `bf16`, `f32`, `f64` and `rat` its use needs, never `int`: at a float format it is the nearest value of that format, and at `rat` it is exact. A decimal that nothing gives a type is a compile error, since no format is the obvious one. A suffix names the format instead: **`0.1f64`**, `0.1f32`, `0.1f16` or `0.1bf16`. So `inc(x) = x + 1;` works on every number type, and `x * 0.5` on every type but `int`.
>
> **`a / b`** divides floats and `rat` values. **`a div b`** and **`a mod b`** are the integer quotient and remainder, and **`a^b`** is a power. **`f64(n)`** converts `n` to `f64`, and **`int(s)`** converts a string to an `int`; such conversions are checked and can fail.
>
> **`==`**, **`!=`**, **`<`**, **`<=`**, **`>`** and **`>=`** compare, giving a **`bool`**, true or false, and `==` compares structure, by value. **`&&`** and **`||`** are logical and and or.

```zed
big = 2^100;                // 2 to the power 100, the exact integer, with no overflow
third = 1r / 3r;             // an exact rational
half = f64(1) / 2.0;         // 2.0 takes the format of f64(1); 1.0 / 2.0 alone would be rejected, since nothing gives it a format
q = 7 div 2;                 // 3
ratio = f64(q) / 2.0;        // conversions are written out; 2.0 takes the format of f64(q)
twice(x: f64) = x * 2.0;     // 2.0 takes the format of x, and x * 2 would work too
// bad = q + 1.5;            // ✗ Numeric literal at a carrier that cannot take it: q is an int, and 1.5 is never an int
```

```text
big   = 1267650600228229401496703205376
third = exactly one third
half  = 0.5, q = 3, ratio = 1.5
```

An `int` is a mathematical integer. It can't overflow, because the compiler picks its machine representation from the range it can prove, and that is a plain machine word wherever a word is enough. So overflow bugs are gone, without the cost of big integers where the range is known. `/` works on fractional types, and integers divide with `div` and `mod`. A `rat` is never rounded, so `0.1r + 0.2r == 0.3r` is true. Mixing `int` and `f64` is a compile error until you write `f64(n)`, because a silent conversion is how a large integer gets rounded with nobody noticing. That cast is checked, so its type also includes the failure value `#inexact` unless the compiler can show the value fits exactly.

Floats of two formats don't mix either, but a literal takes the format of the value it meets. With `x: f64`, `x * 2.0` multiplies by the `f64` `2.0`. With `q: int`, `q * 2.0` is a compile error, because a decimal literal is never an `int`: write `q * 2`, or `f64(q) * 2.0` for a float. The error message lists every fix that compiles, each with the value it gives. A decimal literal is read once, straight into the format its use needs, so `0.1` at an `f64` is the `f64` nearest one tenth, never a narrower value widened, which is where precision would go missing.

### Strings

A string's type says how its text is stored, and you say what you index it by, such as *code points*, the numbers Unicode assigns to characters.

**Syntax:** `"text"`, `"${expression}"`, `a ++ b`, `text::codepoints[i]`

> [!NOTE]
> **`x::word`** reads a fact about `x` that the compiler knows, such as `x::len` from [Step 10](#step-10-the-change-from-the-day-before). **`text::codepoints`** and **`text::u8`** view a string by code point or by UTF-8 unit, which is one byte of its encoding. A **`char32`** is one code point, distinct from an integer, and `char32("Z")` constructs one.

```zed
name = "Zed";
line = "total: ${2 + 3}";            // "total: 5"
title = "never" ++ "the" ++ "less";
z = name::codepoints[0];             // the first code point, a char32
```

```text
line = "total: 5", title = "nevertheless", z = char32("Z")
```

String literals are UTF-8. `Utf8String`, `Utf16String` and `Utf32String` are separate types, one per encoding, and `U8String` holds 8-bit units with no encoding checked. You pick what you index by, such as code points (of type `char32`) or UTF-8 units, through a named view read with `::`, like `text::codepoints` or `text::u8`, and a `U8String` has no code point view. A bare `text[i]` is rejected, because what position `i` means and what it costs depend on the encoding, and code that assumes one character per position tends to break on the first non-English text. `++` builds a rope (a tree of string pieces) in O(1), so joining strings in a loop doesn't go quadratic.

### Structs

A struct is a record of named fields, compared by value and copied with changes.

**Syntax:** `struct Name { field: type, field: type = default }`, `Name(field: value)`, `x with { field = value }`, `Name.method = expression;`

> [!NOTE]
> **`field: T = default`** in a struct declaration gives a field a default value. **`x with { field = value }`** copies `x` with those fields changed. **`Name.method = expression;`** defines a method whose body is one expression.

```zed
struct Point { x: f64, y: f64 }
struct Circle { center: Point, radius: f64 = 1 }

p = Point(x: 1, y: 2);
moved = p with { x = 3 };
unit = Circle(center: p);

Point.norm = (x * x + y * y).sqrt;
size = p.norm;
```

```text
p = Point(x: 1.0, y: 2.0), unchanged
moved = Point(x: 3.0, y: 2.0)
unit = Circle(center: Point(x: 1.0, y: 2.0), radius: 1.0)
size = the square root of 5.0, about 2.236
```

When the compiler can see that the original of a `with` copy isn't used again, the copy is an update in place with no allocation. Two ordinary struct declarations with the same fields are the same type. There are no classes, no inheritance and no object identity. A struct is just a value, so nothing can change it behind your back, and the compiler is free to copy it or share it.

### Atoms, unions and match

An atom is like an enum value that needs no declaration, a union is a choice of types, and `match` takes a union apart.

**Syntax:** `#name`, `#name(args)`, `type T = A | B`, `match x { pattern -> value, ... }`

> [!NOTE]
> **`#name(args)`** is an atom that carries data, its *payload*. **`type Name = T;`** gives a name to a type. **`match x { pattern -> value, ... }`** picks the first arm whose pattern fits `x`. In a pattern, **`field:`** reads that field into a name of the same spelling, as it builds a field from one in a struct value. **`pi`** is the constant.

```zed
// Point and Circle are the structs from Structs above.
struct Rect { lo: Point, hi: Point }
type Shape = Circle | Rect;
type Light = #red | #amber | #green;

// Circle(radius:) matches a Circle and binds its radius field to the name radius.
area(s: Shape) = match s {
  Circle(radius:) -> pi * radius * radius,
  Rect(lo:, hi:) -> (hi.x - lo.x) * (hi.y - lo.y),
};

next(positional l: Light) = match l {
  #red -> #green,
  #green -> #amber,
  #amber -> #red,
};
```

```text
input: Circle with radius 2.0, Rect from (0.0, 0.0) to (3.0, 2.0), #red
area of the Circle = 4 pi, about 12.566
area of the Rect   = 6.0
next(#red)         = #green
```

If a function can return an atom, the function's result type includes it in a union. Atoms with payloads (data carried inside the atom), such as `#c(f64) | #f(f64)`, tell apart values of the same shape. A `match` must cover every case, so when you add a member to `Light`, the compiler points you to each `match` that doesn't handle it yet. If the compiler can't establish that, it shows a value no arm handles or the region it could not resolve. An arm that earlier arms already cover is also rejected.

### Generics and interfaces

Generic code uses type variables with no declaration, and an interface describes what a value must have.

**Syntax:** `type Name(T) = ...`, `interface Name { ... }`

> [!NOTE]
> **`type Name(T) = ...;`** names a type with a type parameter `T`. **`interface Name { ... }`** lists fields and laws, and any value that has them fits it. **`s.last`** is the value at the highest key, here the last element, and **`s.first`** the value at the lowest. Either gives the atom **`#none`**, which means there is nothing here, if `s` is empty.

```zed
type Stack(T) = [T];
push(s: Stack(T), x: T) = s ++ [x];
top(s: Stack(T)) -> T | #none = s.last;

interface Named { name: Utf8String }
hello(positional n: Named) = "Hi, ${n.name}";
```

```text
input: s = [1, 2], x = 3, n = { name: "Ann" }
push(s: [1, 2], x: 3) = [1, 2, 3]
top(s: [1, 2, 3])     = 3
top(s: [])            = #none
hello(n)              = "Hi, Ann"
```

An unbound capitalized name that is used at least twice in a signature, or in the signature and the body, is a type variable. Written only once, it is treated as a typo and rejected. Interfaces are structural: any value on which `name` resolves to a `Utf8String` fits `Named`, with no `implements` clause, so a type can fit an interface its author never heard of. An interface can also hold laws, claims about its operations that the compiler proves or tests, so the algebra behind `><` (the parallel reduction covered below), from `Monoid` (an associative operator with an identity value, one that leaves the other operand unchanged, as 0 does for `+`) to `CommRing` (rules for addition and multiplication, including `a * b == b * a`), is ordinary library code.

### Modules

Each file is a module, and an import names what it brings in.

**Syntax:** `import a.b;`, `import a.b as c;`, `import a.b.{x, y};`, `local`

> [!NOTE]
> **`import a.b;`** imports the module `a.b` whole, **`import a.b as c;`** under the name `c`, and **`import a.b.{x, y};`** only the names listed. **`local`** before a definition keeps it private to its module. **`@name`** is an *annotation*: a claim or request that the compiler acts on or checks, such as `@hash` below.

```zed
import geometry.shapes.{Point, dist};

far = dist(Point(x: 0, y: 0), Point(x: 3, y: 4));
```

```text
far = 5.0, if geometry.shapes defines dist as straight-line distance
(the snippet doesn't show that module)
```

Everything in a file is exported unless marked `local`, and there are no wildcard imports, so you can always tell by reading where a name came from. The build pins each import to the content hash of what it resolved to, with the annotation `@hash`, so the same source builds the same program on any machine, and a dependency upgrade shows up as a visible edit.

## Failure is a value

### `else` and `?.`

A function that can fail returns a union with a failure atom in it, and these two forms handle that atom.

**Syntax:** `T | #someFailure`, `x else fallback`, `x?.field`

> [!NOTE]
> **`x?.field`** reads a field if `x` has one, and passes the failure along if `x` is a failure. **`#syntaxError`** is the failure for text that doesn't parse. In the code, `parse: ...;` declares a function and its type, with the body elsewhere, and the `pos` in the atom's payload says where the parse failed.

```zed
parse: (Utf8String) -> Config | #syntaxError(pos: int);

conf = parse(text) else defaultConfig;
port = parse(text)?.server?.port else 8080;
```

```text
input: text parses, with server.port = 9000
conf = the parsed Config, port = 9000

input: text gives #syntaxError(pos: 3)
conf = defaultConfig, port = 8080
```

There are no exceptions and no null, because in most languages both are ways to fail that a function's type doesn't mention. In Zed the type lists every failure a call can give, and the compiler follows each one to where it is handled. An atom of a named union, such as `Light`, is data and not a failure, so `else` keeps it unless you name it: `x else #red -> #green`.

A `Config | #syntaxError` is not a `Config`. A lookup's failure passes through arithmetic and calls, so if `m[k]` looks up a key that a map `m` may lack, `1 + m[k]` has type `int | #notFound`. The failure stays in the type until you handle it. A reduction, which merges many values into one, never applies its operator to a failure: if any of the values is one, the result is the failures, for the reasons [Step 6](#step-6-adding-values-that-may-be-failures) shows on the sales data.

The compiler also adds a failure only where it can't rule it out. `a div b` has type `int` when `b` can be shown never to be zero, and `int | #divByZero` when it can't. `xs[i]` is plain `T` when `i` is known to be in range. Prove the bound, and the failure and its run-time check both disappear.

### Failures in a pipeline

Failures sit in collections as ordinary values, so you can test for them and choose what to do with them.

**Syntax:** `r is T`, `r is not T`, `m >< op` and `f(m)` on a map `m` that holds failures

> [!NOTE]
> **A merge `m >< op`, and passing `m` to a function whose parameter type has no failures,** run `op` or the function when no value of `m` is a failure, and otherwise give the failures without running it. Nothing in the text shows this step, so every error message that it leads to shows where each failure came out. **`read(path)`** reads a file through the program's `Files` port; it is short for the lookup `fs[path]`. A failed read gives **`#ioError`**, a failed port.

```zed
results = files.map(f -> read(f)).map(t -> parse(t));

good = results.where(r -> r is Config);
bad = results.where(r -> r is not Config);
```

**input: `files`**

<table>
<tr><th><code>i</code></th><th><code>file</code></th></tr>
<tr><td><code>0</code></td><td><code>a.cfg</code></td></tr>
<tr><td><code>1</code></td><td><code>b.cfg</code></td></tr>
<tr><td><code>2</code></td><td><code>c.cfg</code></td></tr>
</table>

**`results` after `.map(f -> read(f))`**

<table>
<tr><th><code>i</code></th><th><code>value</code></th></tr>
<tr><td><code>0</code></td><td>a.cfg's text</td></tr>
<tr><td><code>1</code></td><td><code>#ioError(...)</code></td></tr>
<tr><td><code>2</code></td><td>c.cfg's text</td></tr>
</table>

**`results` after `.map(t -> parse(t))`**

<table>
<tr><th><code>i</code></th><th><code>value</code></th></tr>
<tr><td><code>0</code></td><td><code>Config</code></td></tr>
<tr><td><code>1</code></td><td><code>#ioError(...)</code></td></tr>
<tr><td><code>2</code></td><td><code>#syntaxError(pos: 3)</code></td></tr>
</table>

**`good`**

<table>
<tr><th><code>i</code></th><th><code>value</code></th></tr>
<tr><td><code>0</code></td><td><code>Config</code></td></tr>
</table>

**`bad`**

<table>
<tr><th><code>i</code></th><th><code>value</code></th></tr>
<tr><td><code>1</code></td><td><code>#ioError(...)</code></td></tr>
<tr><td><code>2</code></td><td><code>#syntaxError(pos: 3)</code></td></tr>
</table>

A file that fails to read or parse doesn't stop the others. Each failure stays under its file's key, next to the successes, so you can split them, count them or report them. The read puts details such as the path in the failure's own fields (`#ioError(op:, path:, why:)`), so you don't have to thread that information through by hand.

What you can't do is ignore them by accident:

```zed
amounts = files.map(f -> int(read(f)));         // int(s) converts text to an int, and can fail
sumAll = amounts >< (+);                        // the sum, or all the failures: + never sees one
```

Where you mean something else, you say so:

```zed
sum1 = amounts.where(a -> a is int) >< (+);     // skip the failures
sum2 = amounts.map(a -> a else 0) >< (+);       // count them as zero
```

```text
input: amounts = 3, #ioError(...), 4
sumAll = #ioError(...)
sum1 = 7
sum2 = 7

input: amounts = 3, 5, 4
sumAll = sum1 = sum2 = 12
```

## Collections

Zed's most fundamental structured data abstraction is the multi-level map: a map whose values can themselves be maps, to any depth. A table of sales by region and product is `region -> sku -> amount`, and `sales[r][s]` follows one *keypath*, the chain of keys that leads to one value. One rule holds everywhere: a keypath leads to exactly one value. Arrays, tables, groups and query results are all this one structure, so instead of a separate API for each container you learn a small set of operations that add, move, drop or reduce levels.

### Everything is a map

Arrays, sets, structs and functions are all maps from keys to values, and you write them and read them in the same way.

**Syntax:** `[a, b, c]`, `{ k -> v }`, `{ a, b }`, `m[k]`

> [!NOTE]
> **`[a, b, c]`** is an array, whose keys are `0`, `1`, `2`. **`{ k -> v, ... }`** is a map written out, and **`{ a, b }`** is a set. **`m.sort(desc x -> x)`** orders the entries by the key the function computes, here from high to low, and numbers them by rank.

```zed
xs = [3, 1, 4, 1, 5];                  // int[0..<5] -> int: keys from 0 up to but not including 5
ages = { "Ann" -> 36, "Bob" -> 41 };   // exact keys {"Ann", "Bob"}, int values
tags = { #red, #green };               // a set: a map from each member to itself

first = xs[0];                         // 3: the index is known to be in range
ann = ages["Ann"];                     // 36: the key is known to be there
// carol = ages["Carol"];              // ✗ Key outside the permission bound: this key can't be there
age = ages[name] else 0;               // name is known only at run time

tens = xs.map(x -> x * 10);            // the same keys, new values
big = tens.where(x -> x > 20);         // the keys that pass keep their values: 0, 2, 4
sorted = tens.sort(desc x -> x);       // new keys 0 to 4; equal values stay in their old order
```

```text
input: name = "Ann", then name = "Zed"
first = 3, ann = 36, tags = { #green, #red }
age = 36, then age = 0
```

The last three lines, drawn the same way:

**`tens`**

<table>
<tr><th><code>i</code></th><th><code>x</code></th></tr>
<tr><td><code>0</code></td><td><code>30</code></td></tr>
<tr><td><code>1</code></td><td><code>10</code></td></tr>
<tr><td><code>2</code></td><td><code>40</code></td></tr>
<tr><td><code>3</code></td><td><code>10</code></td></tr>
<tr><td><code>4</code></td><td><code>50</code></td></tr>
</table>

**`big`**

<table>
<tr><th><code>i</code></th><th><code>x</code></th></tr>
<tr><td><code>0</code></td><td><code>30</code></td></tr>
<tr><td><code>2</code></td><td><code>40</code></td></tr>
<tr><td><code>4</code></td><td><code>50</code></td></tr>
</table>

**`sorted`**

<table>
<tr><th><code>rank</code></th><th><code>x</code></th></tr>
<tr><td><code>0</code></td><td><code>50</code></td></tr>
<tr><td><code>1</code></td><td><code>40</code></td></tr>
<tr><td><code>2</code></td><td><code>30</code></td></tr>
<tr><td><code>3</code></td><td><code>10</code></td></tr>
<tr><td><code>4</code></td><td><code>10</code></td></tr>
</table>

An array is a map whose keys are `0..<n`, a set is a map from each key to itself, a struct is a map from field names to values, and a function is a map too. So `xs[i]`, `f(x)` and `p.x` are all lookups, and the same operations work on all of them, except that an operation that visits every key needs a finite set of keys: a function over all of `int` can be called, but `group` or `==` on it is rejected. `K -> V` has a value at every key of `K`, while `K ->? V` may lack some keys, so a lookup can give `#notFound`. A nested map is stored in whichever layout suits the code that reads it. Your code never names the layout, so the compiler may pick a different one without your code changing.

### Grouping

`group` buckets the entries of a map by a key you compute, and `rekey` replaces the key.

**Syntax:** `m.group(x -> key)`, `m.rekey(x -> key)`

> [!NOTE]
> **`m.rekey(x -> key)`** replaces each entry's key with one computed from its value. **`#collision`** is the failure for two entries that landed on one key where a claim that the key is unique was wrong.

```zed
// users : UserId -> User
byCity = users.group(u -> u.city);      // City ->? (UserId -> User)
// byId = users.rekey(u -> u.id);       // ✗ Collision: id is not known to be unique
```

With three sample users, `group` adds the `city` level above the keys that were already there:

**input: `users`**

<table>
<tr><th><code>id</code></th><th><code>user</code></th></tr>
<tr><td><code>1</code></td><td><code>Ann, Oslo</code></td></tr>
<tr><td><code>2</code></td><td><code>Bob, Lima</code></td></tr>
<tr><td><code>3</code></td><td><code>Cid, Oslo</code></td></tr>
</table>

**`byCity`**

<table>
<tr><th><code>city</code></th><th><code>id</code></th><th><code>user</code></th></tr>
<tr><td><code>Lima</code></td><td><code>2</code></td><td><code>Bob, Lima</code></td></tr>
<tr><td rowspan="2"><code>Oslo</code></td><td><code>1</code></td><td><code>Ann, Oslo</code></td></tr>
<tr><td><code>3</code></td><td><code>Cid, Oslo</code></td></tr>
</table>

`group` adds a level, so nothing can be lost. The inner map keeps the users' original keys, exactly those of that city's users, which is why the inner arrow is `->`. Only cities with users occur, and each group is nonempty. Where SQL's `GROUP BY` must aggregate right away, a group here is just a level of the map, which you can reduce, read or reshape later. Since `rekey` can make two entries land on one key, the compiler demands evidence that the new key is unique, such as a function it can see never collides. If it can't see that, the error names the key expression and the evidence that would make it legal. A claim it can't prove, such as `@injective` (this function never gives two inputs one output), is an error too. The error offers a form you write instead, which groups by the new key and checks each group at run time, so its result type gains `#collision`. When two entries really do collide, it shows both. No value ever silently overwrites another in Zed.

### Remapping

A remap states the shape a map has and the shape you want, and the compiler does the moving.

If you know spreadsheets, a remap is close to a pivot table. Moving a field between the Rows and Columns areas shows the same data under a different arrangement of keys, as a remap moves the levels of keys, and a field in the Values area summed with Sum corresponds to a reduction such as `region >< (+)`. The difference is that a pivot table combines whatever lands in one cell whether or not you asked, while a remap merges nothing unless a `><` says how. A remap's result is also an ordinary map of any depth, not a two-axis report.

**Syntax:** `m as (pattern) into (pattern)`

```zed
transposed = matrix as (r -> c -> v) into (c -> r -> v);
ranking = scores as (name -> s) into (desc s -> name -> s);

// totals = sales as (region -> sku -> amount) into (region -> amount);   // ✗ Collision: two skus land on one region
totals = sales as (region -> sku -> amount) into (region -> sku >< (+) -> amount);
```

On small sample tables:

**input: `matrix`**

<table>
<tr><th><code>r</code></th><th><code>c</code></th><th><code>v</code></th></tr>
<tr><td rowspan="3"><code>0</code></td><td><code>0</code></td><td><code>1</code></td></tr>
<tr><td><code>1</code></td><td><code>2</code></td></tr>
<tr><td><code>2</code></td><td><code>3</code></td></tr>
<tr><td rowspan="3"><code>1</code></td><td><code>0</code></td><td><code>4</code></td></tr>
<tr><td><code>1</code></td><td><code>5</code></td></tr>
<tr><td><code>2</code></td><td><code>6</code></td></tr>
</table>

**`transposed`**

<table>
<tr><th><code>c</code></th><th><code>r</code></th><th><code>v</code></th></tr>
<tr><td rowspan="2"><code>0</code></td><td><code>0</code></td><td><code>1</code></td></tr>
<tr><td><code>1</code></td><td><code>4</code></td></tr>
<tr><td rowspan="2"><code>1</code></td><td><code>0</code></td><td><code>2</code></td></tr>
<tr><td><code>1</code></td><td><code>5</code></td></tr>
<tr><td rowspan="2"><code>2</code></td><td><code>0</code></td><td><code>3</code></td></tr>
<tr><td><code>1</code></td><td><code>6</code></td></tr>
</table>

**input: `scores`**

<table>
<tr><th><code>name</code></th><th><code>s</code></th></tr>
<tr><td><code>Ann</code></td><td><code>90</code></td></tr>
<tr><td><code>Bob</code></td><td><code>70</code></td></tr>
<tr><td><code>Cid</code></td><td><code>90</code></td></tr>
</table>

**`ranking`**, with `rank` the level that `desc s` adds:

<table>
<tr><th><code>rank</code></th><th><code>name</code></th><th><code>s</code></th></tr>
<tr><td rowspan="2"><code>0</code></td><td><code>Ann</code></td><td><code>90</code></td></tr>
<tr><td><code>Cid</code></td><td><code>90</code></td></tr>
<tr><td><code>1</code></td><td><code>Bob</code></td><td><code>70</code></td></tr>
</table>

**input: `sales`**

<table>
<tr><th><code>region</code></th><th><code>sku</code></th><th><code>amount</code></th></tr>
<tr><td rowspan="2"><code>East</code></td><td><code>A1</code></td><td><code>5</code></td></tr>
<tr><td><code>B2</code></td><td><code>3</code></td></tr>
<tr><td><code>West</code></td><td><code>A1</code></td><td><code>2</code></td></tr>
</table>

**`totals`**

<table>
<tr><th><code>region</code></th><th><code>amount</code></th></tr>
<tr><td><code>East</code></td><td><code>8</code></td></tr>
<tr><td><code>West</code></td><td><code>2</code></td></tr>
</table>

In `transposed`, a value at row `r` and column `c` moves to row `c` and column `r`. A remap is another way of writing what `group`, `rekey` and `sort` do, and both forms compile to the same thing. In the `ranking` line, putting `desc s` in key position sorts by score, and keeping `name` as a level below it means that two people with the same score can't collide. A remap can move keys around, add levels or drop whole entries, but it can't overwrite a value. The rejected `totals` line asks it to. Here is `sales` with the `sku` level removed, as that line would leave it:

**`sales` with the `sku` level removed**

<table>
<tr><th><code>region</code></th><th><code>amount</code></th><th><code>sku</code> it came from</th></tr>
<tr><td rowspan="2"><code>East</code></td><td>✗ <code>5</code></td><td><code>A1</code></td></tr>
<tr><td>✗ <code>3</code></td><td><code>B2</code></td></tr>
<tr><td><code>West</code></td><td><code>2</code></td><td><code>A1</code></td></tr>
</table>

The key `East` leads to two values, so the result is not a map. The error lists the ways out, and the last `totals` line is one of them. A shortened version of the error:

```text
error: this remap would map one key to many values
  the `(region, sku)` keypaths collapse onto `region`, but their values survive.
  drop the values too:         into (region -> sku -> _)
  or keep the inner key:       into (region -> sku -> amount)
  or say how the values merge: into (region -> sku >< op -> amount)
```

Here is a table with one more level, so you can follow each value as the levels move:

```zed
// revenue : region -> year -> sku -> amount
bySku = revenue as (region -> year -> sku -> amount) into (sku -> region -> year -> amount);
perYear = revenue as (region -> year -> sku -> amount) into (sku -> year -> region >< (+) -> amount);
years = revenue as (region -> year -> sku -> amount) into (region -> year -> _);

// bad = revenue as (region -> year -> sku -> amount) into (sku -> year -> amount);   // ✗ Collision: two regions land on one keypath
```

Each row is one keypath and its value. `bySku` has the same four values as `revenue`, reached by new keypaths. `perYear` first moves the levels, then collapses `region`, and `years` drops the values and keeps the keys down to `year`:

**input: `revenue`**

<table>
<tr><th><code>region</code></th><th><code>year</code></th><th><code>sku</code></th><th><code>amount</code></th></tr>
<tr><td rowspan="3"><code>East</code></td><td rowspan="2"><code>2024</code></td><td><code>A1</code></td><td><code>5</code></td></tr>
<tr><td><code>B2</code></td><td><code>3</code></td></tr>
<tr><td><code>2025</code></td><td><code>A1</code></td><td><code>4</code></td></tr>
<tr><td><code>West</code></td><td><code>2025</code></td><td><code>A1</code></td><td><code>2</code></td></tr>
</table>

**`bySku`**

<table>
<tr><th><code>sku</code></th><th><code>region</code></th><th><code>year</code></th><th><code>amount</code></th></tr>
<tr><td rowspan="3"><code>A1</code></td><td rowspan="2"><code>East</code></td><td><code>2024</code></td><td><code>5</code></td></tr>
<tr><td><code>2025</code></td><td><code>4</code></td></tr>
<tr><td><code>West</code></td><td><code>2025</code></td><td><code>2</code></td></tr>
<tr><td><code>B2</code></td><td><code>East</code></td><td><code>2024</code></td><td><code>3</code></td></tr>
</table>

**`perYear` before summing over `region`**

<table>
<tr><th><code>sku</code></th><th><code>year</code></th><th><code>region</code></th><th><code>amount</code></th></tr>
<tr><td rowspan="3"><code>A1</code></td><td><code>2024</code></td><td><code>East</code></td><td><code>5</code></td></tr>
<tr><td rowspan="2"><code>2025</code></td><td><code>East</code></td><td><code>4</code></td></tr>
<tr><td><code>West</code></td><td><code>2</code></td></tr>
<tr><td><code>B2</code></td><td><code>2024</code></td><td><code>East</code></td><td><code>3</code></td></tr>
</table>

**`perYear` after summing over `region`**

<table>
<tr><th><code>sku</code></th><th><code>year</code></th><th><code>amount</code></th></tr>
<tr><td rowspan="2"><code>A1</code></td><td><code>2024</code></td><td><code>5</code></td></tr>
<tr><td><code>2025</code></td><td><code>6</code></td></tr>
<tr><td><code>B2</code></td><td><code>2024</code></td><td><code>3</code></td></tr>
</table>

**`years`**

<table>
<tr><th><code>region</code></th><th><code>year</code></th><th><code>year</code></th></tr>
<tr><td rowspan="2"><code>East</code></td><td><code>2024</code></td><td><code>2024</code></td></tr>
<tr><td><code>2025</code></td><td><code>2025</code></td></tr>
<tr><td><code>West</code></td><td><code>2025</code></td><td><code>2025</code></td></tr>
</table>

A set is a map from each item to itself, so each region's years form a set, and the value column of `years` repeats the key. What that means is set membership: a keypath either exists or it doesn't. This table shows it, with `yes` meaning "this keypath exists". The `exists` column is only an illustration on this page. `years` has no such column, and a program can't read one.

**`years`, read as which keypaths exist**

<table>
<tr><th><code>region</code></th><th><code>year</code></th><th><code>exists</code></th></tr>
<tr><td rowspan="2"><code>East</code></td><td><code>2024</code></td><td><code>yes</code></td></tr>
<tr><td><code>2025</code></td><td><code>yes</code></td></tr>
<tr><td><code>West</code></td><td><code>2025</code></td><td><code>yes</code></td></tr>
</table>

The constraint on every remap is this: no two values may end up at the same keypath through the map. The rejected `bad` line breaks it:

**`bad`, the levels moved and `region` removed**

<table>
<tr><th><code>sku</code></th><th><code>year</code></th><th><code>amount</code></th><th><code>region</code> it came from</th></tr>
<tr><td rowspan="3"><code>A1</code></td><td><code>2024</code></td><td><code>5</code></td><td><code>East</code></td></tr>
<tr><td rowspan="2"><code>2025</code></td><td>✗ <code>4</code></td><td><code>East</code></td></tr>
<tr><td>✗ <code>2</code></td><td><code>West</code></td></tr>
<tr><td><code>B2</code></td><td><code>2024</code></td><td><code>3</code></td><td><code>East</code></td></tr>
</table>

The keypath `(A1, 2025)` leads to both 4 and 2. The other two keypaths lead to one value each, but the compiler judges from the pattern and not from the data, so it would reject the line even for an input with only those rows. What that leaves is:

- **Moving levels**, or packing them into a tuple key, as in `into ((sku, year) -> region -> amount)`. Each value keeps a keypath of its own.
- **Changing a key** in a way the compiler can see is one-to-one, as `k + 1` is, or **adding a level above a key**, as `desc s` does above, since the old key is still there below it.
- **Dropping a level along with everything under it**, as `years` does. Nothing merges, because no value survives. This is the only way to drop a level without saying how to merge.
- **Collapsing a level with `><`**, as `perYear` does, which is the one way to merge values.

A dictionary built in a loop keeps the last value written to a key without a word, and a database raises a duplicate-key error while the program runs; [Step 5](#step-5-daily-totals) compares the three on the sales data. In Zed the collision is a compile error, and any merge is visible in the text. It also helps performance: since each value has a place of its own, threads can write results without locks, and merge code is needed only where a merge is written. And a rejected remap tells you something about your data: the key you tried to drop is what told those values apart.

### Reducing

A reduction merges the values of one level into one value, using an operator you name.

**Syntax:** `m >< op`, `m >< op else fallback`, `(pattern >< op -> value)`, `m.foldl(init, op)`

> [!NOTE]
> **`m >< op else d`** gives `d` as the answer for an empty collection; without it, the result type includes **`#empty`**, a reduction with nothing to reduce. **`min`** and **`max`** work as operators for `><`. **`.sum`** reduces the innermost level to its sum. **`m.foldl(init, op)`** and **`m.foldr(init, op)`** fold from the left or the right, for an operator that is not associative. **`@associative`** and **`@commutative`** claim that an operator has that property. **`unordered`** after `m >< op` gives up the floating-point result that is the same at any core count, in exchange for speed.

```zed
total = readings >< (+);
longest = words.map(w -> w.len) >< max else 0;
pivot = sales as (i -> s) into (s.region -> s.product -> i >< (+) -> s.amount);
```

On small sample data:

**input: `readings`**

<table>
<tr><th><code>i</code></th><th><code>value</code></th></tr>
<tr><td><code>0</code></td><td><code>2</code></td></tr>
<tr><td><code>1</code></td><td><code>5</code></td></tr>
<tr><td><code>2</code></td><td><code>3</code></td></tr>
</table>

**`total`**

<table>
<tr><th><code>total</code></th></tr>
<tr><td><code>10</code></td></tr>
</table>

**input: `words`**

<table>
<tr><th><code>i</code></th><th><code>w</code></th></tr>
<tr><td><code>0</code></td><td><code>to</code></td></tr>
<tr><td><code>1</code></td><td><code>be</code></td></tr>
<tr><td><code>2</code></td><td><code>not</code></td></tr>
</table>

**`longest` before `>< max`**

<table>
<tr><th><code>i</code></th><th><code>len</code></th></tr>
<tr><td><code>0</code></td><td><code>2</code></td></tr>
<tr><td><code>1</code></td><td><code>2</code></td></tr>
<tr><td><code>2</code></td><td><code>3</code></td></tr>
</table>

**`longest` after `>< max`**

<table>
<tr><th><code>longest</code></th></tr>
<tr><td><code>3</code></td></tr>
</table>

**input: `sales`**

<table>
<tr><th><code>i</code></th><th><code>sale</code></th></tr>
<tr><td><code>0</code></td><td><code>East, pen, 5</code></td></tr>
<tr><td><code>1</code></td><td><code>West, pen, 2</code></td></tr>
<tr><td><code>2</code></td><td><code>East, ink, 3</code></td></tr>
<tr><td><code>3</code></td><td><code>East, pen, 4</code></td></tr>
</table>

**`pivot` before summing over `i`**

<table>
<tr><th><code>region</code></th><th><code>product</code></th><th><code>i</code></th><th><code>amount</code></th></tr>
<tr><td rowspan="3"><code>East</code></td><td><code>ink</code></td><td><code>2</code></td><td><code>3</code></td></tr>
<tr><td rowspan="2"><code>pen</code></td><td><code>0</code></td><td><code>5</code></td></tr>
<tr><td><code>3</code></td><td><code>4</code></td></tr>
<tr><td><code>West</code></td><td><code>pen</code></td><td><code>1</code></td><td><code>2</code></td></tr>
</table>

**`pivot` after summing over `i`**

<table>
<tr><th><code>region</code></th><th><code>product</code></th><th><code>amount</code></th></tr>
<tr><td rowspan="2"><code>East</code></td><td><code>ink</code></td><td><code>3</code></td></tr>
<tr><td><code>pen</code></td><td><code>9</code></td></tr>
<tr><td><code>West</code></td><td><code>pen</code></td><td><code>2</code></td></tr>
</table>

The `pivot` line builds a table of sales by region and product. `i >< (+)` collapses the level `i`, adding the amounts that land on the same region and product.

Merging is always written out, with `><` or a named form such as `.sum`, `.count` or `foldl`. `><` runs in parallel, so except on floating-point values, which have their own rule below, the operator must be associative, and commutative too if the level has no order of its own; [Step 7](#step-7-totals-per-region) shows both properties on numbers. `+` and `max` have both. For your own operators you state them with `@associative` and `@commutative`, as below. These properties decide how the reduction may run: the same line can be a plain loop on one core or a tree across all of them.

```zed
struct Moments { n: int, sum: rat }

@associative @commutative
combine(positional a: Moments, positional b: Moments) =
  Moments(n: a.n + b.n, sum: a.sum + b.sum);

// values : [rat]
m = values.map(x -> Moments(n: 1, sum: x)) >< combine else Moments(n: 0, sum: 0r);
```

With three values:

**input: `values`**

<table>
<tr><th><code>i</code></th><th><code>x</code></th></tr>
<tr><td><code>0</code></td><td><code>1r</code></td></tr>
<tr><td><code>1</code></td><td><code>2r</code></td></tr>
<tr><td><code>2</code></td><td><code>3r</code></td></tr>
</table>

**`m` before `>< combine`**

<table>
<tr><th><code>i</code></th><th><code>value</code></th></tr>
<tr><td><code>0</code></td><td><code>Moments(n: 1, sum: 1r)</code></td></tr>
<tr><td><code>1</code></td><td><code>Moments(n: 1, sum: 2r)</code></td></tr>
<tr><td><code>2</code></td><td><code>Moments(n: 1, sum: 3r)</code></td></tr>
</table>

**`m` after `>< combine`**

<table>
<tr><th><code>m</code></th></tr>
<tr><td><code>Moments(n: 3, sum: 6r)</code></td></tr>
</table>

For `combine`, the compiler derives both laws from `+` on the fields. In general, a proved law lets the compiler regroup freely, while a claim that was only tested permits one fixed grouping and can still be wrong, and the report says which you have. If an operator isn't associative, use `foldl` or `foldr` to say which way to fold. A reduction over nothing can't be silently wrong: the `else` gives the answer for an empty collection, and without it the result type includes `#empty`, unless the operator has an identity or the collection is known not to be empty.

Floating-point sums get special care. `samples >< (+)` adds the floats in one fixed balanced grouping, so the result is the same bits however the work was split and however many cores ran it, about as fast as a plain loop, with an error that grows with the logarithm of the count rather than the count. When cancellation matters, `samples >< (+) compensated` carries the rounding error of each addition along the same grouping, at a few times the cost. If you need the exact sum, add the values as `rat` and round once. If you would rather have speed than the fixed grouping, you ask for it, and it shows in the type: `samples >< (+) unordered`. Your own floating-point operator needs no law: with none, the reduction runs on one fixed grouping over the collection's order, so it gives the same bits at any core count.

### Pushing into a map

A map can be filled by pushing values to its keys, where a reducer says how values at one key merge.

**Syntax:** `name: K ->? V with reducer(op)`, `name[k] <- v`. In the code, `w.len` is the length of `w`.

```zed
hist: int ->? int with reducer((+));
for w in words { hist[w.len] <- 1; };

same = words.group(w -> w.len).count;   // the same table, written as a pull
```

With four words, `hist` gets one push per word, and `same` reaches the same table through a group:

**input: `words`**

<table>
<tr><th><code>i</code></th><th><code>w</code></th></tr>
<tr><td><code>0</code></td><td><code>a</code></td></tr>
<tr><td><code>1</code></td><td><code>to</code></td></tr>
<tr><td><code>2</code></td><td><code>be</code></td></tr>
<tr><td><code>3</code></td><td><code>not</code></td></tr>
</table>

**`hist` pushes**

<table>
<tr><th><code>i</code></th><th><code>push</code></th></tr>
<tr><td><code>0</code></td><td><code>[1] &lt;- 1</code></td></tr>
<tr><td><code>1</code></td><td><code>[2] &lt;- 1</code></td></tr>
<tr><td><code>2</code></td><td><code>[2] &lt;- 1</code></td></tr>
<tr><td><code>3</code></td><td><code>[3] &lt;- 1</code></td></tr>
</table>

**`hist`**

<table>
<tr><th><code>len</code></th><th><code>n</code></th></tr>
<tr><td><code>1</code></td><td><code>1</code></td></tr>
<tr><td><code>2</code></td><td><code>2</code></td></tr>
<tr><td><code>3</code></td><td><code>1</code></td></tr>
</table>

**`same` before `.count`**

<table>
<tr><th><code>len</code></th><th><code>i</code></th><th><code>w</code></th></tr>
<tr><td><code>1</code></td><td><code>0</code></td><td><code>a</code></td></tr>
<tr><td rowspan="2"><code>2</code></td><td><code>1</code></td><td><code>to</code></td></tr>
<tr><td><code>2</code></td><td><code>be</code></td></tr>
<tr><td><code>3</code></td><td><code>3</code></td><td><code>not</code></td></tr>
</table>

**`same` after `.count`**

<table>
<tr><th><code>len</code></th><th><code>n</code></th></tr>
<tr><td><code>1</code></td><td><code>1</code></td></tr>
<tr><td><code>2</code></td><td><code>2</code></td></tr>
<tr><td><code>3</code></td><td><code>1</code></td></tr>
</table>

Sometimes it's clearer to say where each value goes (a push) than where each value comes from (a pull). `hist` can take pushes from many places, and `reducer((+))` adds up the values that land on one key. Because a push only contributes a value and never reads or overwrites one, parallel code can push with no locks. Without the reducer, the compiler has to prove that no two pushes land on one key, and otherwise rejects the program. Pushing and pulling compile to the same thing, so writing it this way doesn't choose the direction the data moves at run time. The compiler picks that for each edge of the graph.

### Joins

A join combines two maps on a shared field, either with a word such as `join` or with a `for` over both.

**Syntax:** `a.join(b, on: #field, kind: #left)`, `a.diff(b, on: #field)`, `for x in a, y in b where ...`

> [!NOTE]
> **`a.join(b, on: #field, kind: #left)`** pairs the entries of `a` and `b` that agree on a field, named with an atom. `kind: #left` makes it a *left join*, which keeps every entry of the left input. **`a.diff(b, on: #field)`** keeps the entries of `a` that have no match in `b`. **`for x in a, y in b where c { e }`** builds a map with one entry `e` per combination that passes `c`.

```zed
// Both inputs are uniquely keyed by OrderId; orderId is their join key.
paid = orders.join(payments, on: #orderId, kind: #left);
// OrderId -> (Order, Payment | #none)

unpaid = orders.diff(payments, on: #orderId);

shipped = for o in orders, s in shipments where o.orderId == s.orderId { (o, s) };
pairs = for i in 0..<n, j in i+1..<n { (i, j) };
```

On small sample data, where `o1` stands for the order with key 1, and `p1` and `s10` likewise:

**input: `orders`**

<table>
<tr><th><code>orderId</code></th><th><code>order</code></th></tr>
<tr><td><code>1</code></td><td><code>o1</code></td></tr>
<tr><td><code>2</code></td><td><code>o2</code></td></tr>
<tr><td><code>3</code></td><td><code>o3</code></td></tr>
</table>

**input: `payments`**

<table>
<tr><th><code>orderId</code></th><th><code>payment</code></th></tr>
<tr><td><code>1</code></td><td><code>p1</code></td></tr>
<tr><td><code>3</code></td><td><code>p3</code></td></tr>
</table>

**`paid`**

<table>
<tr><th><code>orderId</code></th><th><code>value</code></th></tr>
<tr><td><code>1</code></td><td><code>(o1, p1)</code></td></tr>
<tr><td><code>2</code></td><td><code>(o2, #none)</code></td></tr>
<tr><td><code>3</code></td><td><code>(o3, p3)</code></td></tr>
</table>

**`unpaid`**

<table>
<tr><th><code>orderId</code></th><th><code>order</code></th></tr>
<tr><td><code>2</code></td><td><code>o2</code></td></tr>
</table>

**input: `shipments`**

<table>
<tr><th><code>shipmentId</code></th><th><code>shipment</code></th></tr>
<tr><td><code>10</code></td><td><code>s10, order 1</code></td></tr>
<tr><td><code>11</code></td><td><code>s11, order 1</code></td></tr>
<tr><td><code>12</code></td><td><code>s12, order 3</code></td></tr>
</table>

**`shipped`**

<table>
<tr><th><code>(orderId, shipmentId)</code></th><th><code>value</code></th></tr>
<tr><td><code>(1, 10)</code></td><td><code>(o1, s10)</code></td></tr>
<tr><td><code>(1, 11)</code></td><td><code>(o1, s11)</code></td></tr>
<tr><td><code>(3, 12)</code></td><td><code>(o3, s12)</code></td></tr>
</table>

**`pairs`, for input `n = 3`**

<table>
<tr><th><code>(i, j)</code></th><th><code>value</code></th></tr>
<tr><td><code>(0, 1)</code></td><td><code>(0, 1)</code></td></tr>
<tr><td><code>(0, 2)</code></td><td><code>(0, 2)</code></td></tr>
<tr><td><code>(1, 2)</code></td><td><code>(1, 2)</code></td></tr>
</table>

A missing match in a left join is the atom `#none`, which the type shows, and not a row of nulls. For a `for` over several collections, the compiler can pick a hash join or a merge join, two standard ways to avoid comparing every pair, instead of two nested loops. Queries and loops compile to the same internal form, so they are optimized together.

> [!NOTE]
> **`with store(...)`** on a map's declaration makes it a stored table: in a file with `store(file(path, format))`, in Postgres with `store(postgres(...))`, or in a key-value store with `store(kv(...))`. Like `reducer`, it is a setting written with `with`.

The code that uses a map doesn't say where the map lives, so this code is the same whether `orders` is in memory, in a file (`with store(file(path, format))`) or in a database (`with store(postgres(...))`). You add that `with store(...)` annotation on the declaration and the join doesn't change, except that a stored map's type gains the failure its store can give, which you have to handle. A map that one function produces and another consumes may never be allocated at all. Where the consumer reads the values in order, each value passes straight to it as soon as it's computed, much as with `yield` in a generator or with a Unix pipe, and Zed needs no `yield` keyword to get this. Memory is needed where values really must be held, such as for a sort, an index built for lookups, a reduction's result, a value with several readers that can't share one pass, and a port or stored map.

Those choices follow from two goals of the language: you shouldn't have to write memory allocation at all, so the compiler is free to decide how to allocate optimally, and allocation should disappear wherever it can. That's why the code above treats `orders` as a map, keyed by order id, and never says whether it is held as a list, a hash table or something else.

### Chunks

`chunkBy` cuts an ordered collection into runs that share a key.

**Syntax:** `m.chunkBy(x -> key)`

> [!NOTE]
> **`m.chunkBy(x -> key)`** splits an ordered collection wherever the computed key changes. Each chunk is a map that keeps its source keys. In the code, `s.first` is a chunk's first value and `s.count` is its number of entries.

```zed
sessions = clicks.chunkBy(c -> c.userId).map(s -> Session(start: s.first.time, count: s.count));
```

With four clicks in time order, `ann`'s clicks at `i` = 1 and `i` = 3 land in different chunks because `bob` clicked between them:

**input: `clicks`**

<table>
<tr><th><code>i</code></th><th><code>click</code></th></tr>
<tr><td><code>0</code></td><td><code>ann, t=10</code></td></tr>
<tr><td><code>1</code></td><td><code>ann, t=12</code></td></tr>
<tr><td><code>2</code></td><td><code>bob, t=15</code></td></tr>
<tr><td><code>3</code></td><td><code>ann, t=20</code></td></tr>
</table>

**`sessions` before `.map`**

<table>
<tr><th><code>run</code></th><th><code>i</code></th><th><code>click</code></th></tr>
<tr><td rowspan="2"><code>0</code></td><td><code>0</code></td><td><code>ann, t=10</code></td></tr>
<tr><td><code>1</code></td><td><code>ann, t=12</code></td></tr>
<tr><td><code>1</code></td><td><code>2</code></td><td><code>bob, t=15</code></td></tr>
<tr><td><code>2</code></td><td><code>3</code></td><td><code>ann, t=20</code></td></tr>
</table>

**`sessions` after `.map`**

<table>
<tr><th><code>run</code></th><th><code>session</code></th></tr>
<tr><td><code>0</code></td><td><code>Session(start: 10, count: 2)</code></td></tr>
<tr><td><code>1</code></td><td><code>Session(start: 15, count: 1)</code></td></tr>
<tr><td><code>2</code></td><td><code>Session(start: 20, count: 1)</code></td></tr>
</table>

If you have ever split a list into runs by hand, you know the easy mistake is forgetting to flush the last group. Here that can't happen, because the last chunk is included. And since a chunk exists only because a click fell into it, `s.first` always has a value, with no `#none` case to handle.

### Vectors and matrices

An array's type can state its size, so shape mismatches are compile-time errors, not run-time errors: Zed is designed to eliminate as many types of run-time error as possible.

**Syntax:** `[T; n]`, `[T; r, c]`, `s * v`, `a.matmul(b)`

> [!NOTE]
> **`[T; n]`** is a vector of `n` values of type `T`, and **`[T; r, c]`** a matrix of `r` rows and `c` columns. **`s * v`** scales a vector or matrix by the number `s`. **`a.matmul(b)`** is the matrix product, and **`dot`** and **`cross`** are the dot and cross products.

```zed
scale(positional s: T, positional v: [T; n]) = s * v;     // result: [T; n]

a: [f64; 2, 3] = [[1, 2, 3], [4, 5, 6]];
b: [f64; 3, 2] = [[1, 0], [0, 1], [1, 1]];
c = a.matmul(b);                                          // [f64; 2, 2]
// d = a.matmul(a);                                       // ✗ Levels of one name with different domains: 3 columns, 2 rows
```

```text
input: s = 2.0, v = [1.0, 2.0]
scale(2.0, [1.0, 2.0]) = [2.0, 4.0]
```

The product, drawn as a map from rows `r` to columns `j` to values `v`:

**`c`**

<table>
<tr><th><code>r</code></th><th><code>j</code></th><th><code>v</code></th></tr>
<tr><td rowspan="2"><code>0</code></td><td><code>0</code></td><td><code>4.0</code></td></tr>
<tr><td><code>1</code></td><td><code>5.0</code></td></tr>
<tr><td rowspan="2"><code>1</code></td><td><code>0</code></td><td><code>10.0</code></td></tr>
<tr><td><code>1</code></td><td><code>11.0</code></td></tr>
</table>

A name in a shape that isn't bound to an integer is a size variable of the signature, so `[T; n, n]` is a square matrix. Dimension checks are ordinary type checks. Between two vectors or matrices `*` is an error, because it could mean several products: you write `matmul`, `dot` or `cross`. `matmul` isn't built in: it's a one-line remap with a reduction, in the same style as the `pivot` above.

## Time and repetition

### Recurrences

A recurrence defines an array by an equation over earlier entries, plus its boundary values.

**Syntax:** `x[i] = f(x[i-1]) with x[-1] = start;`

> [!NOTE]
> **`i in 0..`** inside an index, as in `d[i in 0..][-1] = i + 1`, defines that entry for every `i` in the range, here every `i` from 0 up. **`min(a, b, ...)`** is the smallest of its arguments.

```zed
running[i] = running[i-1] + xs[i] with running[-1] = 0;

d[i][j] = min(d[i-1][j] + 1, d[i][j-1] + 1, d[i-1][j-1] + cost(a[i], b[j]))
  with d[-1][j in -1..<b::len] = j + 1, d[i in 0..][-1] = i + 1;
```

With `xs` = 3, 1, 4, with `a` and `b` arrays of the code points of "ab" and "ac", and with a `cost` of 0 for equal characters and 1 otherwise, `d[1][1]` is the edit distance, 1. The last table shows `d` as a grid with its boundary values, which are read but aren't entries of the result:

**input: `xs`**

<table>
<tr><th><code>i</code></th><th><code>x</code></th></tr>
<tr><td><code>0</code></td><td><code>3</code></td></tr>
<tr><td><code>1</code></td><td><code>1</code></td></tr>
<tr><td><code>2</code></td><td><code>4</code></td></tr>
</table>

**`running`**

<table>
<tr><th><code>i</code></th><th><code>v</code></th></tr>
<tr><td><code>0</code></td><td><code>3</code></td></tr>
<tr><td><code>1</code></td><td><code>4</code></td></tr>
<tr><td><code>2</code></td><td><code>8</code></td></tr>
</table>

**`d`**

<table>
<tr><th><code>i</code></th><th><code>j</code></th><th><code>v</code></th></tr>
<tr><td rowspan="2"><code>0</code></td><td><code>0</code></td><td><code>0</code></td></tr>
<tr><td><code>1</code></td><td><code>1</code></td></tr>
<tr><td rowspan="2"><code>1</code></td><td><code>0</code></td><td><code>1</code></td></tr>
<tr><td><code>1</code></td><td><code>1</code></td></tr>
</table>

**`d` as a grid, with its boundary values**

<table>
<tr><th></th><th><code>j = -1</code></th><th><code>j = 0</code></th><th><code>j = 1</code></th></tr>
<tr><th><code>i = -1</code></th><td><code>0</code></td><td><code>1</code></td><td><code>2</code></td></tr>
<tr><th><code>i = 0</code></th><td><code>1</code></td><td><code>0</code></td><td><code>1</code></td></tr>
<tr><th><code>i = 1</code></th><td><code>2</code></td><td><code>1</code></td><td><code>1</code></td></tr>
</table>

The code reads as it would on a whiteboard. The first line is a running total. The second is edit distance, the fewest single-character changes that turn one string into another, and it needs no explicit table and no choice of memoization (keeping each result for reuse) or fill order. The `with` clauses give the edges of the table: `d[-1][j]` is `j + 1` and `d[i][-1]` is `i + 1` for every `i` from 0 up, the costs against an empty string. The compiler reads the dependencies and picks a plan: it fills the table across your cores in dependency order if you need most of it, and memoizes on demand if you only touch part of it. In most languages, moving between those two plans means rewriting the code.

The compiler also recognizes some computations that look serial and runs them in parallel. An equation states only what each entry depends on, so nothing ties it to the order a written loop would fix:

```zed
cur[i] = max(xs[i], cur[i-1] + xs[i]) with cur[-1] = 0;
best = cur >< max else 0;

state[i] = csvStep(state[i-1], text::codepoints[i]) with state[-1] = #outsideQuotes;
```

With `xs` = 2, -3, 4, -1, 2, `best` is 5. For the text `a"b"`, if `csvStep` switches state at each quote character:

**input: `xs`**

<table>
<tr><th><code>i</code></th><th><code>x</code></th></tr>
<tr><td><code>0</code></td><td><code>2</code></td></tr>
<tr><td><code>1</code></td><td><code>-3</code></td></tr>
<tr><td><code>2</code></td><td><code>4</code></td></tr>
<tr><td><code>3</code></td><td><code>-1</code></td></tr>
<tr><td><code>4</code></td><td><code>2</code></td></tr>
</table>

**`cur`**

<table>
<tr><th><code>i</code></th><th><code>v</code></th></tr>
<tr><td><code>0</code></td><td><code>2</code></td></tr>
<tr><td><code>1</code></td><td><code>-1</code></td></tr>
<tr><td><code>2</code></td><td><code>4</code></td></tr>
<tr><td><code>3</code></td><td><code>3</code></td></tr>
<tr><td><code>4</code></td><td><code>5</code></td></tr>
</table>

**`state`**

<table>
<tr><th><code>i</code></th><th><code>char</code></th><th><code>state</code></th></tr>
<tr><td><code>0</code></td><td><code>a</code></td><td><code>#outsideQuotes</code></td></tr>
<tr><td><code>1</code></td><td><code>"</code></td><td><code>#insideQuotes</code></td></tr>
<tr><td><code>2</code></td><td><code>b</code></td><td><code>#insideQuotes</code></td></tr>
<tr><td><code>3</code></td><td><code>"</code></td><td><code>#outsideQuotes</code></td></tr>
</table>

The first recurrence is maximum subarray, the largest sum of neighboring entries. Its step has the form `max(x, c + x)`, and composing two such steps gives a step of the same form, so composition is associative and the compiler runs the recurrence as a parallel scan, which computes all the running results across many cores. The second walks a CSV file with a small state machine. Because the states are finite, the compiler can write each character's effect as a table from state to state. Composing tables is associative, so each core composes the tables for its part of the text, and the parts combine afterward:

<table>
<tr><th>start state</th><th>after <code>a"</code></th><th>after <code>b"</code></th><th>after <code>a"b"</code></th></tr>
<tr><td><code>#outsideQuotes</code></td><td><code>#insideQuotes</code></td><td><code>#insideQuotes</code></td><td><code>#outsideQuotes</code></td></tr>
<tr><td><code>#insideQuotes</code></td><td><code>#outsideQuotes</code></td><td><code>#outsideQuotes</code></td><td><code>#insideQuotes</code></td></tr>
</table>

One core computes the table for `a"` and another the table for `b"` without knowing the state at the start of its part. Reading the first table and then the second gives the table for the whole text, `#outsideQuotes` to `#outsideQuotes`, which agrees with the last row of `state`.

### Loops

A loop describes one step, and the loop as a whole is a value holding the final state and the history.

**Syntax:** `loop { x' = f(x) with x = start; until done; }`, `loop t { while c; ... }`, `run.x`, `run::frames`

> [!NOTE]
> **`loop { ... }`**, without a name after `loop`, is a loop with no step counter. **`run::frames`** is every step of the loop `run`, as a map from step number to that step's values. **`x.patch(edit)`** applies an edit to a map or document and gives the new version.

```zed
sim = loop {
  pos' = pos + vel * dt with pos = p0;
  vel' = vel + accel(pos) * dt with vel = v0;
  until pos'.x > bound;
};

final = sim.pos;
history = sim::frames;
steps = sim::len;
```

Following only the `x` part, with `dt` = 1, `pos` starting at 0, `vel` at 1, `accel` always 1 and `bound` = 2, `final.x` is 3 and `steps` is 2. The starting values aren't part of `sim::frames`:

**`sim::frames`**

<table>
<tr><th><code>t</code></th><th><code>pos.x</code></th><th><code>vel.x</code></th></tr>
<tr><td><code>0</code></td><td><code>1</code></td><td><code>2</code></td></tr>
<tr><td><code>1</code></td><td><code>3</code></td><td><code>3</code></td></tr>
</table>

Both updates here read the old `pos`, so they don't race and their order doesn't matter. Each step writes each variable once, so a data race can't be written. Every read in a step sees the same snapshot of the previous step, so you need no temporary variables to keep a simultaneous update straight.

`sim::frames` is every step of the run, kept only if you read it. If you don't, the compiler keeps only the steps the loop still reads, so you never choose between a ring buffer and a full log by hand. Reading it is how you write undo:

```zed
run = loop t {
  while t < edits::len;
  doc' = doc.patch(edits[t]) with doc = empty;
};

previous = run::frames[run::len - 2]?.doc else empty;
```

With two edits `e1` and `e2`, and with `empty` the empty document:

**input: `edits`**

<table>
<tr><th><code>t</code></th><th><code>edit</code></th></tr>
<tr><td><code>0</code></td><td><code>e1</code></td></tr>
<tr><td><code>1</code></td><td><code>e2</code></td></tr>
</table>

**`run::frames`**

<table>
<tr><th><code>t</code></th><th><code>doc</code></th></tr>
<tr><td><code>0</code></td><td><code>empty.patch(e1)</code></td></tr>
<tr><td><code>1</code></td><td><code>that.patch(e2)</code></td></tr>
</table>

`previous` is the document after `e1`. With no edits, or just one, the lookup finds no frame and `previous` is `empty`.

The versions share structure, so keeping them all doesn't copy the document each time, although the history still uses memory.

### Methods and the next value

A method is a function on a struct, and it can define the struct's next version with the same `'` that a loop uses.

**Syntax:** `Type.method() { field' = ...; }`, `x.method()`, `x*.method()`. [Step 11](#step-11-pens-left-on-the-shelf) of the worked example introduces all three.

```zed
struct Counter { n: int, peak: int }

Counter.bump(positional by) -> int {
  n' = n + by;
  peak' = max(peak, n + by);
  return n;
}

start = Counter(n: 0, peak: 0);
after, was = start.bump(2);
```

```text
after = Counter(n: 2, peak: 2), was = 0
start = Counter(n: 0, peak: 0), unchanged
```

Here `n'` is the value of `n` in the next version of this struct. The method doesn't change `start`: it returns a new `Counter` and its declared result, and you have to take both. In a loop body, a `*` makes a call look like mutation: `prev = c*.bump(3);` replaces `c` in the loop's next step. So no call changes a value you hold unless the text shows a `*`, which makes state changes easy to find by reading. Side effects go only through ports, including foreign calls and logging, as [Ports](#ports) below explains.

### Only what's needed runs

A value no result depends on doesn't have to be computed, so unused fields and unbounded ranges cost nothing extra.

**Syntax:** `for i in n.. { ... }`, `.first`. `n..` counts up from `n` with no end.

```zed
stats(positional data: [f64]) {
  n = f64(data::len);
  mean = data.sum / n;
  sd = (data.map(x -> (x - mean)^2).sum / n).sqrt;
  return { mean:, sd: };      // short for { mean: mean, sd: sd }
}

m = stats([1, 2, 3]).mean;         // sd is never computed

firstPrime = (for i in 2.. { i }).where(isPrime).first;
```

```text
stats([1, 2, 3]): n = 3.0, mean = 6.0 / 3.0 = 2.0
m = 2.0, and sd has not run

firstPrime before .where = 2, 3, 4, 5, ...
firstPrime before .first = 2, 3, 5, ...
firstPrime = 2
```

A caller that reads `.mean` doesn't pay for `sd`, and you don't need two versions of the function or a flag. Zed isn't lazy in the Haskell sense, where a value is computed when first read: any evaluation order that gives the same value is legal, and the compiler chooses by cost. The `firstPrime` search runs over an unbounded range. The compiler may try candidates in parallel, and once a prime is found and every smaller candidate has been ruled out, the larger ones can be canceled.

## The outside world

### Ports

Ports are declared channels to the outside world, and they are the only way a program reaches it.

**Syntax:** `main(input: T) -> (output: U) { output <- value; }`

> [!NOTE]
> **`Stream(T)`** is a port type: a sequence of values of type `T` that arrive over time.

```zed
main(req: Stream(Query)) -> (resp: Stream(Answer)) {
  resp <- req.map(q -> answer(q));
}
```

```text
input: req delivers q1, then q2
resp carries answer(q1), then answer(q2)
```

Ports are files, sockets, clocks, devices, databases and the like. They are declared in `main`'s header or as stored collections, which are maps declared `with store(...)`. Foreign calls and logging go through ports too. Everything else is a pure value, so Zed needs no effect system (type annotations that record side effects). It also means the compiler can reorder, parallelize or skip anything that isn't a port operation, since nothing else can be observed. Reading a port gives you a value, and `<-` pushes one out. So a server, a batch job and a pipeline are all the same kind of thing: a function from input ports to output ports.

Runs repeat exactly, apart from a short list such as the order that messages arrive at a port and running out of a resource. Inputs and arrival order can be recorded, so you can replay a failing run in a test.

### Timeouts and retries

A port's reliability settings are declared on the port, and the ones that can fail show up in its type.

**Syntax:** `with timeout(d)`, `with retry(n, backoff: b)`, `with bound(n, overflow: policy)`

> [!NOTE]
> **`with timeout(d)`** sets a deadline, and **`#timeout`** is the failure when it passes. **`with retry(n, backoff: b)`** adds `n` more attempts with a wait `b` between them, where `#fixed(d)` waits up to `d`. **`with bound(n, overflow: policy)`** limits a queue to `n` entries and says what happens when it is full: the writer waits (`#block`), the oldest entry is dropped (`#dropOldest`), or the write fails (`#full`). In the code, **`u8`** is an integer from 0 to 255, so `[u8]` is an array of bytes, and `0.2r with units("s")` is 0.2 seconds.

```zed
cache: Utf8String ->? [u8]
  with store(kv(endpoint))
  with timeout(0.2r with units("s"))
  with retry(2, backoff: #fixed(0.1r with units("s")));

hit = cache[key] else fetch(key);
```

```text
input: key is in the cache
hit = the cached bytes

input: key isn't in the cache, or the read fails, or 0.2 seconds pass
hit = fetch(key)
```

With this `timeout`, a read of `cache` is `[u8] | #ioError | #timeout | #notFound`, and the program has to deal with that, here by treating anything other than a hit as a miss. In most languages a timeout is an exception nothing forces you to catch. `retry` adds no failure member, and the timeout covers all the attempts together. Pure code never times out, because a computation's finishing time isn't a value.

Retries, hedged requests (a second copy of a slow request), circuit breakers (refusing calls for a while after repeated failures), rate limits and failover (switching to a replacement server) are declared on the port in the same way, so the policy sits in one place and not in wrapper code around each call. The compiler permits retries only for operations that are safe to repeat, so a write that may already have landed needs a guarantee that doing it twice has the effect of doing it once (idempotence) before it can be retried. Queues declare what happens when they are full (`#block`, `#dropOldest` or `#full`), so every queue has a limit, and by default a writer waits when it is full.

### Databases

A database table is declared as a map on a store, and its schema is checked at build time.

**Syntax:** `name: K ->? V with store(...)`

> [!NOTE]
> **`sql(path)`** reads a table's schema, the columns and types it declares, from an SQL file. **`#none`** in a stored row's type stands for a NULL column, and **`#dbError`** is the failure when the database fails.

```zed
orders: OrderId ->? { total: rat, note: Utf8String | #none }
  with store(postgres(dbUrl, table: "orders", schema: sql("db/orders.sql")));

n = orders[id]?.note;     // Utf8String | #none | #notFound | #dbError
```

**input: `orders`**

<table>
<tr><th><code>id</code></th><th><code>total</code></th><th><code>note</code></th></tr>
<tr><td><code>1</code></td><td><code>9r</code></td><td><code>"gift"</code></td></tr>
<tr><td><code>2</code></td><td><code>4r</code></td><td><code>NULL</code></td></tr>
</table>

**`n`, for each `id`**

<table>
<tr><th><code>id</code></th><th><code>n</code></th></tr>
<tr><td><code>1</code></td><td><code>"gift"</code></td></tr>
<tr><td><code>2</code></td><td><code>#none</code></td></tr>
<tr><td><code>3</code></td><td><code>#notFound</code></td></tr>
</table>

If the database can't answer, `n` is `#dbError` for any `id`.

You read a stored table with the same `[key]` as any other map, and the same `where` that is a loop over a map in memory may run as a SQL `WHERE` clause here. The schema check compares your declaration with the SQL schema and needs no live connection: a column that allows NULL read as non-optional, or an unbounded string written to a `varchar(80)`, is a compile error at this line, where elsewhere it would fail a request in production. At startup, the program compares the columns it uses with the real database. On a port that supports transactions, such as Postgres, writes made in one step of the program form one transaction, and you never write `begin` or `commit`.

### Incremental updates

When an input changes, the compiler can update the affected results or recompute them in full, and `@memoized` asserts that a value is kept for reuse.

**Syntax:** `@memoized`

> [!NOTE]
> **`@memoized`** makes the build fail if this value isn't kept for reuse (memoized).

```zed
// sales is keyed by SaleId; each sale has a region and an amount.
@memoized
report = sales
  .group(s -> s.region)
  .map(rows -> rows.map(s -> s.amount).sum);
```

Here are three sales, shown as region and amount. If sale 7 then changes from 5 to 6, East's total becomes 9 and West's stays 2:

**input: `sales`**

<table>
<tr><th><code>saleId</code></th><th><code>sale</code></th></tr>
<tr><td><code>7</code></td><td><code>East, 5</code></td></tr>
<tr><td><code>8</code></td><td><code>West, 2</code></td></tr>
<tr><td><code>9</code></td><td><code>East, 3</code></td></tr>
</table>

**`report` before `.map`**

<table>
<tr><th><code>region</code></th><th><code>saleId</code></th><th><code>sale</code></th></tr>
<tr><td rowspan="2"><code>East</code></td><td><code>7</code></td><td><code>East, 5</code></td></tr>
<tr><td><code>9</code></td><td><code>East, 3</code></td></tr>
<tr><td><code>West</code></td><td><code>8</code></td><td><code>West, 2</code></td></tr>
</table>

**`report` after `.map`**

<table>
<tr><th><code>region</code></th><th><code>sum</code></th></tr>
<tr><td><code>East</code></td><td><code>8</code></td></tr>
<tr><td><code>West</code></td><td><code>2</code></td></tr>
</table>

Inside the `.map`, East's `rows.map(s -> s.amount)` is `{ 7 -> 5, 9 -> 3 }`, whose `.sum` is 8.

Incremental updates need no annotation. When an input changes, the change goes through the same graph as a new batch of values (a *wave*), and only what it affects is recomputed, unless a full recomputation would cost less. Changing one sale's amount updates its region's total, and moving a sale to another region updates both. The update stops wherever nothing downstream can see a difference. Spreadsheets, build systems and reactive user interfaces each build this by hand. In Zed the compiler does it, and an incremental result always equals what a full recomputation would give.

This also powers live editing: a change to your source code is one more wave on one more port, so a running program can pick up the edit without a restart. By default the edited program reruns on the recorded inputs, so no extra code is needed. A run whose input history isn't kept, such as a server's, continues from its current loop values instead, and an edit that changes the type of a loop variable, or renames or removes one, must supply a migration, code that converts the old values.

## Checks at compile time

### Ranges and refinements

A type can state a range or a condition on its values.

**Syntax:** `int[lo..=hi]`, `x.refine(p)`, `@ensure`

> [!NOTE]
> **`x.refine(p)`** is `x`, or the failure **`#invalid`** if the condition `p` fails. The check runs at run time unless the compiler can settle it first. A range or condition in a type, such as a parameter's `int[0..=10]`, is different: the compiler has to prove it, and if it can't, the build fails and the error offers `refine` as the check you write yourself. **`@ensure`** on a definition forbids even the run-time checks you wrote in it: each condition has to be proved instead.

```zed
struct Span { lo: int, hi: int[lo..] }

width(positional s: Span) = s.hi - s.lo;   // inferred: int[0..]
// bad = Span(lo: 3, hi: 1);               // ✗ Argument outside its parameter's refinement: hi must be at least lo

@ensure odd(positional x) = (x * 2 + 1).refine(v -> v < 100);
                                           // inferred: x <= 49
a = odd(12);
// b = odd(60);                            // ✗ Undischargeable `@ensure`: 60 > 49
```

```text
input: s = Span(lo: 1, hi: 4)
width(s) = 3, a = 25
```

The compiler tracks ranges, and relations between fields, through arithmetic without any annotations from you. That is how it removes bounds checks and picks the smallest machine representation. With `@ensure`, the compiler has to push the condition back onto the inputs and reject the program if it can't prove them safe, so the check moves to compile time.

A field's range may name another field. The compiler reasons about such bounds with linear arithmetic (sums of variables times constants), and no SMT solver, a general theorem prover, is involved. The checks come from a small set of procedures that always finish, so the compile time is predictable and the error message says exactly what stopped the proof.

### Units and taint

Units and taint are labels you attach to a value with `with`.

**Syntax:** `with units("...")`, `with taint(#label)`

> [!NOTE]
> **`with taint(#label)`** attaches a *taint*, a label for where a value came from, such as user input. It follows the value through the program until a function removes it. Like units, taint is a facet.

```zed
v = 3.0 with units("m/s");
t = 2.0 with units("s");
d = v * t;                 // has units "m"
// e = v + t;              // ✗ Units that differ where an operation requires equal ones: m/s + s

render: (Utf8String with taint(#clean)) -> Html;
comment = input with taint(#userInput);

// page = render("<p>" ++ comment ++ "</p>");   // ✗ Taint at a sink whose parameter does not take it: user input reaches render
page = render("<p>" ++ escapeHtml(comment) ++ "</p>");
```

```text
input: input = "<b>"
d = 6.0 in m
page = render of "<p>&lt;b&gt;</p>", if escapeHtml escapes as usual
```

These are *facets*: extra facts about a value, tracked through every operation at compile time. Units and taint have no run-time cost. Units catch mistakes in formulas that a plain `f64` lets through. Here `render` declares that it takes only clean text and `escapeHtml` is the function that removes the taint, so passing user input straight through is a type error. Any program can define a facet of its own in the same way, such as a latency or a parity.

### Cost

Annotations turn performance requirements into build failures.

**Syntax:** `f::cost`, `@cost(b)`, `@fused`, `@noalloc`

> [!NOTE]
> **`f::cost`** reads a function's computed upper bound on *work*, its total number of operations, and **`f::depth`** its bound on *parallel depth*, the longest chain of operations that must run one after another. **`@cost(b)`** states a bound on work, **`@fused`** says no intermediate collection is built, and **`@noalloc`** says the code uses no memory beyond registers. **`log`** is the natural logarithm.

```zed
@cost(xs::len)
@fused
sumSquares(positional xs: [f64]) = xs.map(x -> x * x) >< (+);

@cost(xs::len * log(xs::len))
ranked(positional xs: [int]) = xs.sort(desc x -> x);

@noalloc
lerp(positional a: f64, positional b: f64, positional t: f64) = a * (1 - t) + b * t;
```

```text
input: [1.0, 2.0, 3.0], [3, 1, 2], 0.0, 10.0, 0.5
sumSquares([1.0, 2.0, 3.0]) = 14.0
ranked([3, 1, 2])           = [3, 2, 1]
lerp(0.0, 10.0, 0.5)        = 5.0

These are the values. This page doesn't work out the bound that f::cost reads
for these functions, beyond what the @cost lines state.
```

Every function has a computed upper bound on its work and its parallel depth, which you can read as `f::cost` and `f::depth`. Where no bound can be proved, they say `#unbounded`. `@cost`, `@fused` and `@noalloc` are assertions about the plan the compiler chose. If one is false, the build fails, so a slowdown in a hot path shows up on the commit that caused it, and not later in production.

## Code that runs at build time

### Partial evaluation

An expression the program needs is computed at build time when its inputs are known then.

**Syntax:** none. It applies to any needed expression with known inputs.

> [!NOTE]
> **`Json.decode(s)`** decodes JSON text into the type expected at the call. **`#parseError`** is the failure for text that doesn't parse into that type. **`compile`**, mentioned below, turns source code held as a value back into a function.

```zed
struct User { id: int, name: Utf8String }

ok: User | #parseError(pos: int, msg: Utf8String) = Json.decode("{\"id\": 5, \"name\": \"John\"}");
// the constant User(id: 5, name: "John")

bad: User | #parseError(pos: int, msg: Utf8String) = Json.decode("{\"id\": \"five\"}");
// the constant #parseError(pos: 7, msg: "expected int for field 'id', got string")
```

```text
ok, bad = constants in the compiled program, with no decoder call at run time
```

Zed has no macro language and no `comptime` keyword. The build uses the same evaluator as a run, with the same meaning, so there's no second language to learn and no gap between what code means at build time and at run time. The JSON decoder above is ordinary Zed. Given a literal, the whole call runs during the build. Given a value only known at run time, the decoder is specialized to `User`, which means compiled for that one type, with the generic field lookups already gone. A regular expression known at build time compiles to a matcher in the same way, with nothing left to interpret. If a program does arrive at run time as data, `compile` turns it into a function using the same machinery.

### Reflection

`::` reads the structure of a type or a declaration, and that read happens at build time.

**Syntax:** `T::fields`, `T::shape`, `T::values`, `x::constraints`, `f::source`

> [!NOTE]
> **`T::fields`** gives a type's fields, by name and type, **`T::shape`** one layer of its structure, and **`T::values`** the set of its values. **`x::constraints`** is what the compiler knows about a value, and **`f::source`** is a function's source code, as a value.

```zed
type Size = #small | #medium | #large;

sizes = Size::values;       // {#large, #medium, #small}: atoms sort by name
names = User::fields;       // the fields of the User struct above, by name and type
```

```text
sizes = { #large, #medium, #small }
names = id, an int, and name, a Utf8String
```

Generic code uses these reads: that's how `Json.decode` knows what `User` looks like. Reflection has no run-time cost, which is why a generic decoder needs neither a code generator nor a slower reflective path.

### Grammars

A grammar describes a text or binary format.

**Syntax:** `struct Name grammar { ... }`, `type T = Utf8String matching grammar { ... }`, `T.parse(s)`, `x.serialize`

> [!NOTE]
> **`grammar { ... }`** after a struct's name makes its fields a *parser*, which turns text into a value, and a *serializer*, which turns the value back into text. In a grammar, **`"("`** is literal text and **`x: T`** a field. **`T.parse(s)`** reads `s` into a value of `T`, and **`x.serialize`** writes `x` back out.

```zed
struct Vec3 grammar { "(" x: f64 "," y: f64 "," z: f64 ")" }

v = Vec3.parse("(1.0, 2.0, 3.0)") else Vec3(x: 0, y: 0, z: 0);
s = v.serialize;       // "(1.0,2.0,3.0)"
```

```text
v = Vec3(x: 1.0, y: 2.0, z: 3.0), s = "(1.0,2.0,3.0)"

input: "(oops)" in place of the literal
v = Vec3(x: 0.0, y: 0.0, z: 0.0), s = "(0.0,0.0,0.0)"
```

Add `grammar` to a struct and its fields become a parser and a serializer for that format. You get one definition for both directions, so the two can't drift apart, and the compiler checks that the round trip gives you back the value. Grammars can be recursive, and the result is ordinary typed data. Here is a calculator, parser and evaluator together. `Prod sep "+"` is a list of `Prod` with `+` between them, `matching` limits a string type to what the grammar accepts, `digit digit*` is a digit followed by any number of digits, and `this` is the value a method was called on:

```zed
struct Sum grammar { terms: Prod sep "+" }
struct Prod grammar { factors: Factor sep "*" }
struct Paren grammar { "(" inner: Sum ")" }
type Number = Utf8String matching grammar { digit digit* };
type Factor = Number | Paren;

Sum.eval = terms.map(t -> t.eval).sum;
Prod.eval = factors.map(f -> f.eval) >< (*);
Paren.eval = inner.eval;
Number.eval = int(this) else 0;

value = Sum.parse("2*(3+4)")?.eval;     // 14, or #syntaxError
```

```text
Sum.parse("2*(3+4)") = a Sum holding one Prod, of 2 and a Paren of 3 + 4
value = 14

input: "2*(" in place of the literal
value = #syntaxError
```

Binary formats work the same way, with the layout given by words such as `bits` (a field's width), `endian` (its byte order) and `length` (its element count), and `u8*` is a run of bytes. This is the layout of a PNG chunk:

```zed
struct Chunk grammar {
  n: int with bits(32) with endian(#big)
  kind: u8* with length(4)
  data: u8* with length(n)
  crc: int with bits(32) with endian(#big)
}
```

```text
input: the bytes 00 00 00 01  49 44 41 54  2A  00 00 00 07
Chunk.parse(input) = Chunk(n: 1, kind: the 4 bytes of "IDAT", data: the 1 byte 2A, crc: 7)
```

### Symbolic math

Programs can read a function, rewrite it and compile it again.

**Syntax:** `f::source`, `expand(e)`, `derivative(e)`

> [!NOTE]
> **`expand(e)`** multiplies out a formula held as source, and **`derivative(e)`** differentiates it. Here the function's parameter has a stated type: `(x: rat) -> ...`.

```zed
p = ((x: rat) -> (x + 1r)^2)::source;
e = expand(p);          // x^2 + 2r * x + 1r
d = derivative(p);      // 2r * x + 2r
```

```text
e = x^2 + 2r * x + 1r
d = 2r * x + 2r
```

The source of a function is a value, and rewriting it is an ordinary program, so algebra and differentiation are library code and not a separate tool. Each rewrite carries a proof that the compiler checks step by step, and the types of the function's parameters are the assumptions, so `(x * y) div y` simplifies to `x` when `y` is known to be at least 1, and not when `y` may be 0. `compile` turns the result back into a function.

## Tests, laws and proofs

### Tests next to the code

A `test` table lists inputs and expected outputs for a definition.

**Syntax:** `f(...) = ... test { input -> output, ... }`

> [!NOTE]
> **`test { input -> output, ... }`** after a definition is a table of test cases, run at build time. **`@exhaustive`** asks for the tests to run on every input of a finite domain.

```zed
double(positional x) = x * 2 test { 0 -> 0, 2 -> 4, -3 -> -6 }
```

```text
double(0), double(2), double(-3) = 0, 4, -6, which match the table
```

Tests live on the definition and run at build time, so they stay next to what they test, and since a table is data, a tool can read or generate it. A function whose domain (its set of possible inputs) the source lists member by member, such as `bool`, is run on every input, and `@exhaustive` asks for the same on any other finite domain, such as `int[1..=9]`.

### Laws

A `law` states a property of your code for the compiler to prove or test.

**Syntax:** `law name(x: T) = expression;`

> [!NOTE]
> **`law name(x: T) = expression;`** claims that a `bool` expression holds for every `x`. The compiler tries to prove it and reports its *grade*, how far it got. A law that isn't proved makes the build fail.

```zed
// double is the function from Tests next to the code above.
law doubleIsSum(x: int) = double(x) == x + x;
law addComm(a: int, b: int) = a + b == b + a;
law sortTwice(xs: [int]) = xs.sort(asc x -> x).sort(asc x -> x) == xs.sort(asc x -> x);
```

```text
input: x = 3; a = 1, b = 2; xs = [3, 1, 2]
doubleIsSum(3): double(3) == 3 + 3, 6 == 6
addComm(1, 2): 1 + 2 == 2 + 1, 3 == 3
sortTwice([3, 1, 2]): sorting twice and once both give [1, 2, 3]

These are single cases. Which grade
the build reports for each of these three laws isn't worked out here, since it
depends on the compiler's rewrites.
```

A test checks the cases you thought of, and a law states what has to hold for every input. The compiler tries to prove a law with a fixed ladder of methods. For a domain whose members the source lists, such as `bool` or a set of atoms, it checks every case, and otherwise it tries the rewrites and automatic proof methods it has. If those fail, the law is tested on generated inputs. It then reports how far it got: exhaustively checked, proved, checked up to a bound, tested, assumed or unknown. A test on generated inputs can find a counterexample but can't prove the law, so a law that isn't exhaustively checked or proved stops the build, and the error shows how far each method got.

The optimizer can use proved laws as rewrites. A `law` that was only tested is never used to rewrite your program. An `@associative` annotation that was only tested can still choose a fixed regrouping, and the report says so.

### Model checking

A loop that collects every reachable state, together with a law over those states, checks a state machine at build time.

**Syntax:** `loop` plus `law`

> [!NOTE]
> **`m.flatMap(x -> list)`** maps each value to a list, with the list's positions as a new level. **`m.image`** is the set of a map's values, **`a.union(b)`** the union of two sets, and **`p.implies(q)`** logical implication. **`x in s`** is true if `x` is a member of `s`. In the code, the loop stops when `R` stops growing.

```zed
type Signal = #red | #green;
struct Junction { ns: Signal, ew: Signal }
type Cmd = #goNs | #goEw | #stop;

advance(positional j: Junction, positional c: Cmd) = match c {
  #goNs -> if j.ew == #red { j with { ns = #green } } else { j },
  #goEw -> if j.ns == #red { j with { ew = #green } } else { j },
  #stop -> Junction(ns: #red, ew: #red),
};

reachable = loop {
  R' = R.union(R.flatMap(j -> [advance(j, #goNs), advance(j, #goEw), advance(j, #stop)]).image)
    with R = { Junction(ns: #red, ew: #red) };
};

law neverBothGreen(ns: Signal, ew: Signal) =
  (Junction(ns: ns, ew: ew) in reachable.R).implies(ns == #red || ew == #red);
```

**`reachable.R`**

<table>
<tr><th><code>state</code></th><th><code>state</code></th></tr>
<tr><td><code>Junction(ns: #green, ew: #red)</code></td><td><code>Junction(ns: #green, ew: #red)</code></td></tr>
<tr><td><code>Junction(ns: #red, ew: #green)</code></td><td><code>Junction(ns: #red, ew: #green)</code></td></tr>
<tr><td><code>Junction(ns: #red, ew: #red)</code></td><td><code>Junction(ns: #red, ew: #red)</code></td></tr>
</table>

Each row is one state, a `Junction` in the set `R`. A set is a map from each member to itself, so the value column repeats the key. The loop reaches these three states in one step, and the next step adds none. None has both lights green, so the law holds.

A loop is a state machine, so the set of states it can reach is a fixpoint (a value one more step doesn't change) you can write in a few lines, and for a finite state space the compiler computes it at build time. `reachable.R` is the final set. A `Junction` with both lights green is a legal value, but no sequence of commands reaches it, and the law checks exactly that. This covers the safety checks you would use TLC, a widely used model checker, for, in the language the system is written in. Liveness (something good eventually happens) must be stated as a bound or a decreasing measure, and properties that rely on fairness (no ready action of the environment is put off forever) can't be expressed. A failed check reports the sequence of steps that reached the bad state, as a value you can replay.

## Under the hood

### Error messages

A compile error says what failed, why, and what would fix it.

**Syntax:** none.

Every error gives the rule that failed and the checker's whole chain of reasoning: each constraint, where it came from and how it reached this line. When the compiler has concrete evidence, such as two keys that collide or a value no `match` arm covers, it shows it. When a proof is missing, it names the expression or region it couldn't resolve. It then lists the repairs that would work, as in the error shown in [Remapping](#remapping) above. The rules that reject a program are fixed lists, so whether a program is accepted never depends on how strong the optimizer is. The one exception is an assertion you write about the plan, such as `@cost` or `@fused`, which checks the plan the compiler chose.

### Calling C, and being called from C

Annotations declare C functions to call and Zed functions to expose to C.

**Syntax:** `@foreign("lib", "symbol")`, `@export("c", "symbol")`, `@stateless`

> [!NOTE]
> **`@foreign("lib", "symbol")`** declares a C function from a library, **`@export("c", "symbol")`** makes a Zed function callable from C, and **`@stateless`** promises that a foreign function has no state, so a call to it can be retried.

```zed
@foreign("m", "cbrt") @stateless cbrt: (positional x: f64) -> f64;

root = cbrt(8) else f64(0);

@export("c", "zed_score")
score(positional a: f64, positional b: f64) = (7 * a + 3 * b) / 10;
```

```text
input: a = 1.0, b = 0.0
root = 2.0, or 0.0 if the foreign call fails
score(1.0, 0.0) = 0.7, and C's zed_score(1.0, 0.0) returns the same
```

A foreign call is an operation on a port, because C code can do anything, and this keeps the rest of the program pure. The declared `-> f64` is the C result, and the call also has a failure type, which is why `root` has an `else`. It takes the same `timeout` word as any other port, and `retry` if the function is marked `@stateless`, a promise about the library that the compiler can't check. Foreign structs declare their memory layout field by field, and C memory is read through that layout, either in place or as a copy. `@export` compiles a function into a shared library with a generated C header. On the LLVM back end (LLVM is a widely used compiler toolkit), C code compiled by Clang (a C compiler) can be inlined into Zed code and optimized along with it.

### Memory

The compiler places all allocation and freeing.

**Syntax:** `@noalloc`, `@preallocated`

> [!NOTE]
> **`@preallocated`** says the code's memory has a bound and is reserved once, on entry. `@noalloc`, from [Cost](#cost) above, says it uses no memory beyond registers.

Most intermediate collections are never allocated at all, as [Joins](#joins) explains, and this stop is about the rest. Zed has no garbage collector and no lifetimes, and ownership annotations appear only on foreign signatures. Zed values can't form cycles, so exact reference counting (freeing a value when a count of its users reaches zero) is enough, and the compiler removes most of it: where a last use is known statically, the free is placed there, with no count at all. A functional update of a value nothing else refers to happens in place. Cyclic data lives in arenas, blocks of memory whose nodes are freed together, or in id-indexed graphs, whose nodes refer to each other by key, so a stale lookup gives `#notFound` and not a dangling pointer. Freeing is spread out across the scheduler's work, so there are no garbage-collection pauses and no long chains of frees. `@noalloc` and `@preallocated` let you assert a bounded footprint and have the build fail if it doesn't hold.

### Parallelism and determinism

The compiler decides what runs in parallel, and the output doesn't change with the number of cores.

**Syntax:** none.

Any two parts of a program with no dependency between them may run at once, and the compiler splits the work using the dependency graph and the laws of each operator. Outputs are bit-identical at any core count, floating-point reductions included, so a test that passes on your laptop means the same on a 64-core server, and a bug seen there can be reproduced on one core. The exceptions are a short, enumerated list: arrival order at ports, the interleaving at an output port that declares one, foreign-call order the program leaves open, `unordered` reductions, and running out of a resource. There is no undefined behavior, except where a foreign library breaks a promise made about it.

### Targets

The same program compiles to several kinds of hardware and platform.

**Syntax:** none.

A program states dependencies and names no threads, addresses or machines, and that is what lets it move between targets. One intermediate representation (the form a compiler holds a program in) sits under everything. Back ends (the compiler stages that generate code) compile it to native multicore code through the MLIR and LLVM compiler toolkits, and to WebAssembly (portable code for browsers and other runtimes), GPUs, distributed dataflow (running parts of the graph on several machines, where the keys of your data decide which machine holds what), hardware synthesis (circuit designs) and microcontrollers. The compiler is written in Zed itself, on top of a small kernel, the core everything else is built on. A program that needs a port its target doesn't have is rejected at build time, and the error names the port and how the program reached it.

## FAQ: You should change the name. Don't you know there's a Zed IDE?

Yes, I know there's a Zed IDE. People remind me of this every day. I have had the zedlang.org domain and @ZedLang Twitter handle since 2012, and I'm not changing the name.

There is enough room in this world for two Zeds. I wish the Zed IDE people all the success in the world, and we can coexist. "I developed it in Zed using Zed" will catch on!

## Creator of Zed

Zed was created by [Luke Hutchison](https://x.com/LH). The design ideas started to coalesce in detail around 2006, with some code developed in intervening years, along with a very detailed and complex spec, which as of the advent of Opus 5.5 became a perfect prompt. Zed is being fully built-out in 2026 from this complex design doc developed over the last 20 years.

The official X account for Zed is [@ZedLang](https://x.com/ZedLang).

## License

Zed is released under the [MIT License](LICENSE).
