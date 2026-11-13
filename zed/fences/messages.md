<!-- The `text` fences of the spec's DESIGN.md and EXAMPLES.md, copied by the sync tool: do not edit. -->

<!-- DESIGN.md:249; section [sec:remap_law] 1 -->
```text
error: Cannot map many values to one key: `into (region -> day -> r)`. Try `into (region -> day -> sku -> _)` instead.
  the `(region, day, sku)` keypaths collapse onto `(region, day)`, but their values survive.
  drop the values too:         into (region -> day -> sku -> _)
      keeps each sku and drops its value
  or keep the inner key:       into (region -> day -> sku -> r)
      keeps each value under its sku
  or say how the values merge: into (region -> day -> sku >< op -> r)
      merges each day's values with op, which must be associative
```

<!-- DESIGN.md:1027; section [sec:level_names] 1 -->
```text
error: Too few names for the 4 levels of `Sales`: `names("region", "sku", "quantitySold")`. Try `names("_", "region", "sku", "quantitySold")` instead.
  1. the facet (1:55)
       type Sales = Utf8String ->? [Utf8String ->? int] with names("region", "sku", "quantitySold");
                                                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  2. the levels of `Sales`, outermost first, with the name each would get
       1. the keys of the outer map, Utf8String: "region"
       2. the positions in the list, int[0..<_]: "sku"
       3. the keys of the inner map, Utf8String: "quantitySold"
       4. the leaf, int: no name is left for it
  3. `names` takes one name for each level and one for the leaf, and "_" leaves a level unnamed
  fixes, each checked here:
    with names("_", "region", "sku", "quantitySold")
    with names("region", "_", "sku", "quantitySold")
    with names("region", "sku", "_", "quantitySold")
    with names("region", "sku", "quantitySold", "_")
```

<!-- DESIGN.md:1045; section [sec:level_names] 2 -->
```text
error: Not a Zed name: `"quantity sold"`. Try `names("region", "day", "sku", "quantitySold")` instead.
  1. the name (1:85)
       type Sales = Utf8String ->? [Utf8String ->? int] with names("region", "day", "sku", "quantity sold");
                                                                                           ^^^^^^^^^^^^^^^
  2. a level name is written as a variable's name is: it starts with a letter or `_`, goes on with letters, digits and `_`, and is not a keyword such as `in`; "quantity sold" has a space after its eighth character
  fixes, each checked here:
    with names("region", "day", "sku", "quantitySold")
    with names("region", "day", "sku", "quantity_sold")
```

<!-- DESIGN.md:1056; section [sec:level_names] 3 -->
```text
error: Two names for one level: `(region: Utf8String) ->? int with names("area", "count")`. Try `(area: Utf8String) ->? int with names("area", "count")` instead.
  1. the name `area`, given by `names` (1:55)
       type Counts = (region: Utf8String) ->? int with names("area", "count");
                                                             ^^^^^^
  2. the name `region`, given by the arrow's parameter (1:16)
       type Counts = (region: Utf8String) ->? int with names("area", "count");
                      ^^^^^^
  3. a level has one name, however it is written
  fixes, each checked here:
    type Counts = (area: Utf8String) ->? int with names("area", "count");
    type Counts = (region: Utf8String) ->? int with names("region", "count");
    type Counts = (region: Utf8String) ->? int with names("_", "count");
```

<!-- DESIGN.md:1105; section [sec:level_names] 4 -->
```text
error: Two levels named `key` in `m : K ->? V` with `V : (key: int) ->? int`: `lookupOr(catalog, "top", { 0 -> 0 })`. Try `lookupOr(catalog as (shelf -> item -> count), "top", { 0 -> 0 })` instead.
  1. the argument (3:14)
       c = lookupOr(catalog, "top", { 0 -> 0 });
                    ^^^^^^^
     its type is Utf8String ->? ((key: int) ->? int), so `V` is (key: int) ->? int at this call
  2. the outer level of `m` is named `key` by the declaration of `lookupOr` (1:43)
       lookupOr(positional m: K ->? V with names("key", "value"), positional k: K, positional d: V) -> V = m[k] else d;
                                                 ^^^^^
  3. the inner level is named `key` by the type of `catalog` (2:27)
       catalog: Utf8String ->? ((key: int) ->? int) with names("shelf", "_", "count") = { "top" -> { 7 -> 2 } };
                                 ^^^
  4. two levels of one map never share a name, since a pattern that binds `key` could not tell them apart
  fixes, each checked here:
    c = lookupOr(catalog as (shelf -> item -> count), "top", { 0 -> 0 });    renames the inner level for this call
    catalog: Utf8String ->? ((item: int) ->? int) with names("shelf", "_", "count") = { "top" -> { 7 -> 2 } };
```

<!-- DESIGN.md:1227; section [sec:level_names] 5 -->
```text
region  day  sku    quantitySold
"east"  0    "B7"   5
"west"  0    "A12"  3
"west"  0    "B7"   1
"west"  1    "A12"  2
```

<!-- DESIGN.md:1260; section [sec:domains] 1 -->
```text
error: No `f64` equals the literal: `x: f64 = 9007199254740993`. Try `x: int = 9007199254740993` instead.
  1. the literal (1:10)
       x: f64 = 9007199254740993;
                ^^^^^^^^^^^^^^^^
     an integer literal can be an int, bf16, f16, f32, f64 or rat, each only where that carrier holds it exactly
     f64 holds every integer up to 9007199254740992, which is 2^53; this one is 2^53 + 1,
       halfway between the f64 values 9007199254740992.0 and 9007199254740994.0
  2. the expected carrier (1:4)
       x: f64 = 9007199254740993;
          ^^^
     the declaration of `x` expects f64
  3. a literal takes a carrier only as one of that carrier's values, and Zed converts no value implicitly
  fixes, each checked here:
    x: int = 9007199254740993;                                      x is exactly 9007199254740993, and its uses take int
    x: rat = 9007199254740993;                                      x is exactly 9007199254740993, and its uses take rat
    x: f64 = 9007199254740992;                                      x is 9007199254740992.0, the nearer f64 by ties to even
    x: f64 = round(9007199254740993r);                              x is the same f64
```

<!-- DESIGN.md:2375; section [sec:theories] 1 -->
```text
trivial models of CommRing
  on one value, #a, with every field returning #a: every law holds.
  on two values, #a | #b:
    mul, one, add, zero, neg, linked by laws mulAssoc, oneMul, mulOne, addAssoc, addComm, addZero, addNeg, distrib, distribRight, mulComm: no model.
      mul cannot be ((x, y) -> #a), by law oneMul: mul(one, a) == a
      mul cannot be ((x, y) -> #b), by law oneMul: mul(one, a) == a
      mul cannot be ((x, y) -> x), by law oneMul: mul(one, a) == a
      mul cannot be ((x, y) -> y), by law mulOne: mul(a, one) == a
      so no choice is left for mul
  models on two values: 0.
  So the model on one value is the only trivial model.
```

<!-- DESIGN.md:2395; section [sec:theories] 2 -->
```text
trivial models of Fano
  on one value, #a: law line1 (c1 != c2 || c2 != c3) does not hold, since on one value every two values are equal.
  on two values, #a | #b:
    c1, c2, c3, c4, c5, c6, c7, linked by laws line1, line2, line3, line4, line5, line6, line7: not decided.
      The report stopped at a choice that leads to no model, so this list may be incomplete:
        with c1: #a, c2: #a, c4: #a
        c3 cannot be #a, by law line1: c1 != c2 || c2 != c3
        c5 cannot be #a, by law line2: c1 != c4 || c4 != c5
        c6 cannot be #a, by law line4: c2 != c4 || c4 != c6
        so law line7: c3 != c5 || c5 != c6 does not hold
      Whether laws like these have a model can take time exponential in the number of fields to decide, so the report does not search on by itself. To list every trivial model, at the cost of that search, write `@exhaustive` before the interface:
        @exhaustive interface Fano(positional T) { ... }
```

<!-- DESIGN.md:2462; section [sec:diagnostics] 1 -->
```text
error: Cannot compare unequal types: `x[1] : int < y[1] : rat`. Try `rat(x[1]) < y[1]` instead.
```

<!-- DESIGN.md:2626; section [sec:diagnostics] 2 -->
```text
error: A decimal literal is never an `int`: `x : int * 2.0`. Try `twice(x: int) = x * 2` instead.
  1. the literal (1:21)
       twice(x: int) = x * 2.0;
                           ^^^
     a decimal literal can be a bf16, f16, f32, f64 or rat, never an int, even when its value is an integer
  2. the expected carrier (1:19)
       twice(x: int) = x * 2.0;
                         ^
     `*` takes two operands of one carrier, and its left operand `x` is int (1:17)
     the declaration of the parameter `x` sets it (1:7)
       twice(x: int) = x * 2.0;
             ^^^^^^
  3. a value of one carrier is not converted to another implicitly, so `x` is not made a float
  fixes, each checked here:
    twice(x: int) = x * 2;           2 takes the int of x; twice(x: 3) is 6
    twice(x: int) = rat(x) * 2.0;    twice is (x: int) -> rat, and twice(x: 3) is 6r
    twice(x: f64) = x * 2.0;         twice is (x: f64) -> f64, and twice(x: 1.5) is 3.0
    twice(x: rat) = x * 2.0;         twice is (x: rat) -> rat, and twice(x: 3r/2r) is 3r
    twice(x) = x * 2.0;              twice is (x: T) -> T for T in bf16 | f16 | f32 | f64 | rat
```

<!-- DESIGN.md:2652; section [sec:diagnostics] 3 -->
```text
error: Nothing gives the literal `2.5` a carrier. Try `y = inc(x: 2.5f64)` instead.
  1. the literal (2:12)
       y = inc(x: 2.5);
                  ^^^
     a decimal literal can be a bf16, f16, f32, f64 or rat, never an int, even when its value is an integer
  2. its use, the argument `x` of `inc` (2:9)
       y = inc(x: 2.5);
               ^^^^^^
     `inc` is declared here with no type written for `x` or its result; the type the checker found for `inc` is `(x: T) -> T for T in int | bf16 | f16 | f32 | f64 | rat` (1:1)
       inc(x) = x + 1;
       ^^^^^^^^^^^^^^^
     `T` is the carrier of both the argument and the result, so the literal takes `T`, and `T` must come from elsewhere: the call has no other argument
  3. the result of the call is bound to `y` (2:1)
       y = inc(x: 2.5);
       ^
     `y` is declared with no type, and a name fixes its value where it is bound, so no read of `y` gives `T` a carrier
  4. an integer literal here would be an `int`; a decimal literal is never an `int`, and no float format or `rat` is the obvious carrier, so Zed does not choose one
  fixes, each checked here:
    y = inc(x: 2.5f64);      the literal is then the f64 2.5
    y = inc(x: 2.5r);        the literal is then exactly 2.5, a rat
    y: f64 = inc(x: 2.5);    the literal is then the f64 2.5
    y: rat = inc(x: 2.5);    the literal is then exactly 2.5, a rat
```

<!-- DESIGN.md:2681; section [sec:diagnostics] 4 -->
```text
error: Nothing gives the integer literals a carrier, and `/` has none at `int`: `q = (1 + 2) / (3 + 4)`. Try `q = (1.0f64 + 2) / (3 + 4)` instead.
  1. the division (1:13)
       q = (1 + 2) / (3 + 4);
                   ^
     `/` takes two operands of one carrier, a float format or rat, and has no arrow at `int`
  2. its left operand (1:5)
       q = (1 + 2) / (3 + 4);
           ^^^^^^^
     `1 + 2` adds two integer literals, so it is a literal too and takes the carrier of what it meets; it meets only the `/`
  3. its right operand (1:15)
       q = (1 + 2) / (3 + 4);
                     ^^^^^^^
     `3 + 4` is a literal in the same way, and it too meets only the `/`
  4. the value of `q` (1:1)
       q = (1 + 2) / (3 + 4);
       ^
     `q` is declared with no type, and a name bound to an operation on literals alone fixes it there, so no read of `q` gives it a carrier
  5. where nothing gives a carrier, an operation on integer literals is an `int`, and `/` has no arrow at `int`; no float format or `rat` is the obvious carrier, so Zed does not choose one
  fixes, each checked here:
    q = (1.0f64 + 2) / (3 + 4);    q is 0.42857142857142855
    q = (1r + 2) / (3 + 4);        q is 3r/7r
    q = (f64(1) + 2) / (3 + 4);    q is 0.42857142857142855
    q: f64 = (1 + 2) / (3 + 4);    q is 0.42857142857142855
    q: rat = (1 + 2) / (3 + 4);    q is 3r/7r
```

<!-- DESIGN.md:2712; section [sec:diagnostics] 5 -->
```text
c.zed:3:47: Cannot pass `#nf` to `ap`, which takes `(T1, T1)`: `k(y : (T1, T1) | #nf)`.
  T1 stands for a part written more than once:
    type T1 = int | #x;
  [1] 2:20: `k` needs this of its argument here
  [2] 2:1: `k` is declared here with no type written for `a` or its result; the type the checker found for `k` is `(T) -> (0, T)`
  [3] 3:47: repair: pass `ap` a value of (T1, T1)
  [4] 3:47: repair: `if y is (T1, T1) { k(y) } else { … }`, with the declaration above written first at the top level of the file, before the function
  [5] 3:47: repair: handle the values that are not (T1, T1) with `else` or `match`
```

<!-- DESIGN.md:2729; section [sec:diagnostics] 6 -->
```text
error: A list level has no string key: `sales[day: "Monday" : Utf8String]`. Try `sales[day: 0]` instead.
  1. the key (3:16)
       x = sales[day: "Monday"];
                      ^^^^^^^^
  2. the level `day`, named in the read (3:11) and by `names` in the type `Sales` (1:71)
       x = sales[day: "Monday"];
                 ^^^
       type Sales = Utf8String ->? [Utf8String ->? int] with names("region", "day", "sku", "quantitySold");
                                                                             ^^^^^
  3. the level `day` is the list `[Utf8String ->? int]`, whose keys are the positions 0, 1, 2, … (1:29)
       type Sales = Utf8String ->? [Utf8String ->? int] with names("region", "day", "sku", "quantitySold");
                                   ^^^^^^^^^^^^^^^^^^^^
  4. a key that shares no value with the keys of its level is an error, not a miss
  fixes, each checked here:
    x = sales[day: 0];             x is { "east" -> { "B7" -> 5 }, "west" -> { "A12" -> 3, "B7" -> 1 } }
    x = sales[sku: "Monday"];      x is { "east" -> [#notFound], "west" -> [#notFound, #notFound] }
    x = sales[region: "Monday"];   x is #notFound
```
