> [!NOTE]
> **Zed is still under construction and is not yet ready for use, but it is coming soon.**
> Releases will be announced at [x.com/zedlang](https://x.com/zedlang). This page describes the language as it will be when finished.

<p align="center">
  <img src="docs/assets/banner.svg" alt="Zed" width="512">
</p>

Zed is a programming language that looks like ordinary code, but has no variables you overwrite and no statement order you have to get right. A Zed program is a set of definitions: each value says what it depends on, and the compiler works out the rest. Because the compiler can see that whole graph of dependencies, it can run your code in parallel, free memory without a garbage collector, recompute only what changed when an input changes and reject many bugs before the program runs.

Here is a complete program. It splits a file on spaces, counts each word, and prints the counts, most common first.

```zed
main(fs: Files) -> (stdout: Lines) {
  text = fs["input.txt"] else "";
  counts = text.split(" ").group(w -> w.lower).count;
  lines = counts as (w -> n) into (desc n -> w -> "${w}: ${n}");
  stdout <- lines.rank;
}
```

`group` collects the words by their lowercase form, and `.count` turns each group into its size. The `as ... into ...` line reshapes that table: `desc n` sorts by count, `w` stays as a level below it so equal counts don't collide, and each value becomes a line of text. `.rank` flattens the nested table into a list numbered in that order, and `<-` writes the lines out.

The program doesn't mention threads, locks or allocation. The compiler can run the grouping on all your cores, and the output is the same, bit for bit, on one core or on sixty-four. A missing file can't crash the program either: the type of `fs["input.txt"]` says the read can fail, and the `else` says what to do when it does.

Three more short examples from the tour below:

```zed
// Two values landing on one key is a compile error, never a silent overwrite.
// totals = sales as (region -> sku -> amount) into (region -> amount);   // ✗ rejected
// Say how they merge: add the amounts for each region.
totals = sales as (region -> sku -> amount) into (region -> sku >< (+) -> amount);

// Edit distance: the equation and its boundary. The compiler picks the table and the fill order.
d[i][j] = min(d[i-1][j] + 1, d[i][j-1] + 1, d[i-1][j-1] + cost(a[i], b[j]))
  with d[-1][j in -1..<b::len] = j + 1, d[i in 0..][-1] = i + 1;

// A database table, checked against its SQL schema at build time.
orders: OrderId ->? { total: rat, note: Utf8String | #none }
  with store(postgres(dbUrl, table: "orders", schema: sql("db/orders.sql")));
```

Zed exists because many systems already recover a graph of values from ordinary code: spreadsheets, optimizing compilers, Spark, build systems, reactive UI frameworks and out-of-order CPUs. In Zed the graph is the program, so one compiler handles parallel scheduling, memory management, incremental updates and many correctness checks from one structure. This doesn't have to make programs longer: the word-count program above is about as long as the same program in Python.

The rest of this page is a tour of the language. Each stop shows a piece of syntax, an example, and what the example means. Snippets stand alone unless they say otherwise, and a name a snippet doesn't define is an input you can assume. A commented-out line marked ✗ is one the compiler rejects.

- [The basics](#the-basics): bindings, functions, numbers, strings, structs, unions, generics, modules
- [Failure is a value](#failure-is-a-value)
- [Collections](#collections): maps, grouping, remapping, reducing, pushing, joins, chunks, matrices
- [Time and repetition](#time-and-repetition): recurrences, loops, methods, running only what's needed
- [The outside world](#the-outside-world): ports, retries, databases, incremental updates
- [Checks at compile time](#checks-at-compile-time): ranges, units, taint, cost
- [Code that runs at build time](#code-that-runs-at-build-time): partial evaluation, reflection, grammars, symbolic math
- [Tests, laws and proofs](#tests-laws-and-proofs)
- [Under the hood](#under-the-hood): error messages, C, memory, parallelism, targets

## The basics

### Bindings

`name = value;` or `name: type = value;`

```zed
total = price * quantity;
price = 12;
quantity = 3;
port: int[1..=65535] = 8080;
```

A binding gives a name to a value, once. It can't be reassigned, and it can be used above the line that defines it, as `price` is here: the order of definitions doesn't matter, only what depends on what. The type is optional, and it can be more exact than in most languages. `int[1..=65535]` means an integer in that range, and the compiler checks it.

### Functions

`f(positional x, y = default) = expression;` or `f(...) -> type { ... }`

```zed
double(positional x) = x * 2;

clamp(positional v, positional lo, positional hi) -> int {
  if v < lo { lo } else if v > hi { hi } else { v }
}

greet(positional name: Utf8String, punct = "!") = "Hi, " ++ name ++ punct;

a = 5.double.clamp(0, 8);        // 8
b = greet("Ann", punct: "?");    // "Hi, Ann?"
hi = greet("Ann", ...);          // a function still waiting for punct
```

Parameters are passed by name unless you mark them `positional`, so a call site says what its arguments mean. Any function can be called with a dot, so `5.double` is `double(5)`, and pipelines read left to right. A `...` in a call leaves the remaining named parameters open and gives you back a function. Parameter types can usually be left out, and the compiler infers them from how the body uses the parameter. `x * 2` takes an `int`; `x * 2n` would take any number type.

### Numbers

`42`, `1.5`, `3r`, `a / b`, `a div b`, `f64(n)`

```zed
big = 2 ** 100;              // no overflow; this is the exact integer
third = 1r / 3r;             // an exact rational
half = 1.0 / 2.0;            // f64
q = 7 div 2;                 // 3
ratio = f64(q) / 2.0;        // conversions are written out
// bad = q + 1.5;            // ✗ rejected: int + f64
```

An `int` is a mathematical integer. It can't overflow, because the compiler picks its machine representation from the range it can prove, and that is a plain machine word wherever a word is enough. `/` works on fractional types, and integers divide with `div` and `mod`. `r` marks an exact rational, so `0.1r + 0.2r == 0.3r` is true. Zed never converts a number for you: mixing `int` and `f64` is a compile error until you write `f64(n)`. That cast is checked, so its type also includes `#inexact` unless the compiler can show the value fits exactly.

### Strings

`"text"`, `"${expression}"`, `a ++ b`, `text::codepoints[i]`

```zed
name = "Zed";
line = "total: ${2 + 3}";            // "total: 5"
title = "never" ++ "the" ++ "less";
z = name::codepoints[0];             // the first code point
```

String literals are UTF-8. Encodings are separate types (`U8String`, `Utf8String`, `Utf16String`, `Utf32String`), and you pick what you index by, such as code points or UTF-8 units, through a named view like `text::codepoints` or `text::u8`. `++` builds a rope in O(1), so joining strings in a loop doesn't go quadratic.

### Structs

`struct Name { field: type, field: type = default }`, `Name(field: value)`, `x with { field = value }`, `Name.method = expression;`

```zed
struct Point { x: f64, y: f64 }
struct Circle { center: Point, radius: f64 = 1.0 }

p = Point(x: 1.0, y: 2.0);
moved = p with { x = 3.0 };
unit = Circle(center: p);

Point.norm = (x * x + y * y).sqrt;
size = p.norm;
```

Constructors take their arguments by name. `with` makes a copy with some fields changed, and when the compiler can see the original isn't used again, the copy is an update in place with no allocation. A method like `norm` is a function with an implicit first parameter whose fields are in scope. Structs compare by value, and two struct declarations with the same fields are the same type. There are no classes, no inheritance and no object identity.

### Atoms, unions and match

`#name`, `#name(args)`, `type T = A | B`, `match x { pattern -> value, ... }`

```zed
struct Rect { lo: Point, hi: Point }
type Shape = Circle | Rect;
type Light = #red | #amber | #green;

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

An atom is a constant that is its own name, with no declaration needed. A union says a value is one of several things, and atoms with payloads such as `#c(f64) | #f(f64)` tell apart values of the same shape. A `match` must cover every case. If the compiler can't establish that, it shows a value no arm handles or the region it could not resolve. An arm that earlier arms already cover is also rejected.

### Generics and interfaces

`type Name(T) = ...`, `interface Name { ... }`

```zed
type Stack(T) = [T];
push(s: Stack(T), x: T) = s ++ [x];
top(s: Stack(T)) -> T | #none = s.last;

interface Named { name: Utf8String }
hello(positional n: Named) = "Hi, ${n.name}";
```

An unbound capitalized name that is used at least twice in a signature, or in the signature and the body, is a type variable, with nothing to declare. Written only once, it is treated as a typo and rejected. Interfaces are structural: any value on which `name` resolves to a `Utf8String` fits `Named`, with no `implements` clause. An interface can also hold laws, so the algebra behind `><` (the parallel reduction covered below), from `Monoid` to `CommRing`, is ordinary library code.

### Modules

`import a.b;`, `import a.b as c;`, `import a.b.{x, y};`, `local`

```zed
import geometry.shapes.{Point, dist};

far = dist(Point(x: 0.0, y: 0.0), Point(x: 3.0, y: 4.0));
```

A file is a module. Everything in it is exported unless marked `local`, and there are no wildcard imports, so you can always tell by reading where a name came from. The build pins each import to the content hash of what it resolved to, with `@hash`.

## Failure is a value

### `else` and `?.`

`T | #someFailure`, `x else fallback`, `x?.field`

```zed
parse: (Utf8String) -> Config | #syntaxError(pos: int);

conf = parse(text) else defaultConfig;
port = parse(text)?.server?.port else 8080;
```

There are no exceptions and no null. A function that can fail says so in its return type, by returning a union with an atom in it. `else` replaces any failure with a fallback, and `?.` reads a field if there is one and passes the failure along if there isn't.

A `Config | #syntaxError` is not a `Config`. Arithmetic and calls on a failure pass it along, so `1 + m[k]` has type `int | #notFound`. The failure stays in the type until you handle it. A reduction is stricter: it is rejected if its operator might be applied to a failure it does not handle, since failures at many keys can't become one result unless you say how.

The compiler also adds failures only where they can really happen. `a div b` has type `int` when `b` can be shown never to be zero, and `int | #divByZero` when it can't. `xs[i]` is plain `T` when `i` is known to be in range. Prove the bound, and the failure and its run-time check both disappear.

### Failures in a pipeline

`r is T`, `r is not T`, `m.allOk`

```zed
results = files.map(f -> read(f)).map(b -> parse(b));

good = results.where(r -> r is Config);
bad = results.where(r -> r is not Config);
```

A file that fails to read or parse doesn't stop the others. A failure is an ordinary value, sitting in the collection next to the successes under the same key, so you can split them, count them or report them. Each one stays under its file's key, and the read puts details such as the path in the failure's own fields (`#ioError(op:, path:, why:)`), so you don't have to thread that information through by hand.

What you can't do is ignore them by accident:

```zed
amounts = files.map(f -> int(read(f)));
// sum = amounts >< (+);                        // ✗ rejected: some amounts may be failures
```

You say what you mean instead:

```zed
sum1 = amounts.where(a -> a is int) >< (+);     // skip the failures
sum2 = amounts.map(a -> a else 0) >< (+);       // count them as zero
sum3 = amounts.allOk >< (+);                    // the sum, or all the failures
```

## Collections

### Everything is a map

`[a, b, c]`, `{ k -> v }`, `{ a, b }`, `m[k]`

```zed
xs = [3, 1, 4, 1, 5];                  // int[0..<5] -> int
ages = { "Ann" -> 36, "Bob" -> 41 };   // exact keys {"Ann", "Bob"}, int values
tags = { #red, #green };               // a set: a map from each member to itself

first = xs[0];                         // 3: the index is known to be in range
ann = ages["Ann"];                     // 36: the key is known to be there
// carol = ages["Carol"];              // ✗ rejected: this key can't be there
age = ages[name] else 0;               // name is known only at run time

big = xs.map(x -> x * 10).where(x -> x > 20).sort(desc x -> x);   // 50, 40, 30
```

An array is a map whose keys are `0..<n`, a set is a map from each key to itself, a struct is a map from field names to values, and a function is a map too. So `xs[i]`, `f(x)` and `p.x` are all lookups, and the same operations work on all of them. `K -> V` has a value at every key of `K`, while `K ->? V` may lack some keys, so a lookup can give `#notFound`. Nested maps are the normal way to hold tables: `Region -> Product -> rat` is a table of sales by region and product, stored in whichever layout suits the code that reads it.

### Grouping

`m.group(x -> key)`, `m.rekey(x -> key)`

```zed
// users : UserId -> User
byCity = users.group(u -> u.city);      // City ->? (UserId -> User)
// byId = users.rekey(u -> u.id);       // ✗ rejected unless id is known to be unique
```

`group` adds a level, so nothing can be lost. The inner map keeps the users' original keys, exactly those of that city's users, which is why the inner arrow is `->`. Only cities with users occur, and each group is nonempty. `rekey` replaces the key, and that can make two entries land on one key, so the compiler demands evidence that the new key is unique, such as a declared key or a function it can see never collides. If it can't see that, the error names the key expression and the evidence that would make it legal. When two entries really do collide, it shows both. No value ever silently overwrites another in Zed.

### Remapping

`m as (pattern) into (pattern)`

```zed
transposed = matrix as (r -> c -> v) into (c -> r -> v);
ranking = scores as (name -> s) into (desc s -> name -> s);

// totals = sales as (region -> sku -> amount) into (region -> amount);   // ✗ rejected
totals = sales as (region -> sku -> amount) into (region -> sku >< (+) -> amount);
```

`as ... into ...` states the shape you have and the shape you want. It is another way of writing what `group`, `rekey` and `sort` do, and both forms compile to the same thing. In the `ranking` line, putting `desc s` in key position sorts by score, and keeping `name` as a level below it means that two people with the same score can't collide. A remap can move keys around, add levels or drop whole entries, but it can't overwrite a value. If you ask it to, as in the rejected `totals` line, you get an error that lists the ways out, and the last `totals` line is one of them. A shortened version of the error, where a keypath is the chain of keys that leads to a value:

```text
error: this remap would map one key to many values
  the `(region, sku)` keypaths collapse onto `region`, but their values survive.
  drop the values too:         into (region -> sku -> _)
  or keep the inner key:       into (region -> sku -> amount)
  or say how the values merge: into (region -> sku >< op -> amount)
```

### Reducing

`m >< op`, `m >< op else fallback`, `(pattern >< op -> value)`, `m.foldl(init, op)`

```zed
total = readings >< (+);
longest = words.map(w -> w.len) >< max else 0;
pivot = sales as (i -> s) into (s.region -> s.product -> i >< (+) -> s.amount);
```

The `pivot` line builds a table of sales by region and product. `i >< (+)` collapses the level `i`, adding the amounts that land on the same region and product.

Merging is always written out, with `><` or a named form such as `.sum`, `.count` or `foldl`. `><` runs in parallel, so it needs an operator that is safe to regroup: `+` and `max` are known to be, and for your own operators you state the law.

```zed
struct Moments { n: int, sum: rat }

@associative @commutative
combine(positional a: Moments, positional b: Moments) =
  Moments(n: a.n + b.n, sum: a.sum + b.sum);

// values : [rat]
m = values.map(x -> Moments(n: 1, sum: x)) >< combine else Moments(n: 0, sum: 0r);
```

For `combine`, the compiler derives both laws from `+` on the fields. In general, a proved law lets the compiler regroup freely, while a claim that was only tested permits one fixed grouping and can still be wrong, and the report says which you have. If an operator isn't associative, use `foldl` or `foldr` to say which way to fold. A reduction over nothing can't be silently wrong: the `else` gives the answer for an empty collection, and without it the result type includes `#empty`, unless the operator has an identity.

Floating-point sums get special care. `samples >< (+)` computes the exact sum and rounds it once, so the result doesn't depend on how the work was split or how many cores ran it. If you'd rather have speed than that guarantee, you ask for it, and it shows in the type: `samples >< (+) unordered`.

### Pushing into a map

`name: K ->? V with reducer(op)`, `name[k] <- v`

```zed
hist: int ->? int with reducer((+));
for w in words { hist[w.len] <- 1; };

same = words.group(w -> w.len).count;   // the same table, written as a pull
```

Sometimes it's clearer to say where each value goes than where each value comes from. `hist` is a map that many places can push to, and `reducer((+))` says how contributions to one key merge. Without the reducer, the compiler has to prove that no two pushes land on one key, and otherwise rejects the program. Pushing and pulling compile to the same thing, so writing it this way doesn't choose the direction the data moves at run time. The compiler picks that for each edge of the graph.

### Joins

`a.join(b, on: #field, kind: #left)`, `a.diff(b, on: #field)`, `for x in a, y in b where ...`

```zed
// Both inputs are uniquely keyed by OrderId; orderId is their join key.
paid = orders.join(payments, on: #orderId, kind: #left);
// OrderId -> (Order, Payment | #none)

unpaid = orders.diff(payments, on: #orderId);

shipped = for o in orders, s in shipments where o.orderId == s.orderId { (o, s) };
pairs = for i in 0..<n, j in i+1..<n { (i, j) };
```

A missing match in a left join is the atom `#none`, which the type shows, and not a row of nulls. A `for` over several collections is a join as well, and the compiler can pick a hash join or a merge join for it instead of two nested loops. Queries and loops compile to the same terms, so they are optimized together.

### Chunks

`m.chunkBy(x -> key)`

```zed
sessions = clicks.chunkBy(c -> c.userId).map(s -> Session(start: s.first.time, count: s.count));
```

`chunkBy` splits an ordered collection wherever the key changes. If you have ever written this by hand, you know the easy mistake is forgetting to flush the last group. Here that can't happen, because the last chunk is included. And since a chunk exists only because a click fell into it, `s.first` is exact, with no `#none` case to handle.

### Vectors and matrices

`[T; n]`, `[T; r, c]`, `s * v`, `a.matmul(b)`

```zed
scale(positional s: T, positional v: [T; n]) = s * v;     // result: [T; n]

a: [f64; 2, 3] = [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0]];
b: [f64; 3, 2] = [[1.0, 0.0], [0.0, 1.0], [1.0, 1.0]];
c = a.matmul(b);                                          // [f64; 2, 2]
// d = a.matmul(a);                                       // ✗ rejected: 3 columns, 2 rows
```

A name in a shape that isn't bound to an integer is a size variable of the signature, so `[T; n, n]` is a square matrix. Dimension checks are ordinary type checks, and the mismatch in the last line is a compile error. `*` scales a vector or matrix by a number. Between two vectors or matrices it is an error, because it could mean several products: you write `matmul`, `dot` or `cross`. `matmul` isn't built in: it's a one-line remap with a reduction, in the same style as the `pivot` above.

## Time and repetition

### Recurrences

`x[i] = f(x[i-1]) with x[-1] = start;`

```zed
running[i] = running[i-1] + xs[i] with running[-1] = 0;

d[i][j] = min(d[i-1][j] + 1, d[i][j-1] + 1, d[i-1][j-1] + cost(a[i], b[j]))
  with d[-1][j in -1..<b::len] = j + 1, d[i in 0..][-1] = i + 1;
```

You write the equation and the boundary cases, as you would on a whiteboard. The first line is a running total. The second is edit distance, and it needs no explicit table and no choice of memoization or fill order. The compiler reads the dependencies and picks a plan: it fills the table across your cores in dependency order if you need most of it, and memoizes on demand if you only touch part of it.

The compiler also recognizes some loops that look serial and runs them in parallel:

```zed
cur[i] = max(xs[i], cur[i-1] + xs[i]) with cur[-1] = 0;
best = cur >< max else 0;

state[i] = csvStep(state[i-1], text::codepoints[i]) with state[-1] = #outsideQuotes;
```

The first recurrence is maximum subarray. The compiler recognizes that its step composes in any grouping, so it runs as a parallel scan. The second walks a CSV file with a small state machine. Because the states are finite, the compiler can tabulate the transitions, and tables compose in any grouping, so a job usually done one character at a time splits across cores.

### Loops and generations

`loop { x' = f(x) with x = start; until done; }`, `run.x`, `run::frames`

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

A loop describes one step: `pos'` is the next value of `pos`, written in terms of the current values. Both updates here read the old `pos`, so they don't race and their order doesn't matter. Each step writes each variable once, so a data race can't be written. After the loop, `sim.pos` is the final value.

`sim::frames` is every step of the run, kept only if you read it. If you don't, the compiler keeps only the steps the loop still reads. If you do, the whole history is there to read. This is how you write undo:

```zed
run = loop t {
  while t < edits::len;
  doc' = doc.patch(edits[t]) with doc = empty;
};

previous = run::frames[run::len - 2].doc else empty;
```

`patch` applies one edit to the document. The versions share structure, so keeping them all doesn't copy the document each time, although the history still uses memory.

### Methods and the next value

`Type.method() { field' = ...; }`, `x.method()`, `x*.method()`

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

Inside a method, `n'` means the same thing it means in a loop: the value of `n` in the next version of this struct. The method doesn't change `start`: it returns a new `Counter` and its declared result, and you have to take both. In a loop body, a `*` makes a call look like mutation: `prev = c*.bump(3);` replaces `c` in the loop's next step. So no call changes anything unless the text shows a `*`.

### Only what's needed runs

`for i in n.. { ... }`, unused fields, `.first`

```zed
stats(positional data: [f64]) {
  n = f64(data::len);
  mean = data.sum / n;
  sd = (data.map(x -> (x - mean) ** 2).sum / n).sqrt;
  return { mean:, sd: };
}

m = stats([1.0, 2.0, 3.0]).mean;      // sd is never computed

firstPrime = (for i in 2.. { i }).where(isPrime).first;
```

Work runs only if a result depends on it. A caller that reads `.mean` doesn't pay for `sd`, and you don't need two versions of the function or a flag. Zed isn't lazy in the Haskell sense: any evaluation order that gives the same value is legal, and the compiler chooses by cost. The `firstPrime` search runs over an unbounded range. The compiler may try candidates in parallel, and once a prime is found and every smaller candidate has been ruled out, the larger ones can be canceled.

## The outside world

### Ports

`main(input: T) -> (output: U) { output <- value; }`

```zed
main(req: Stream(Query)) -> (resp: Stream(Answer)) {
  resp <- req.map(q -> answer(q));
}
```

A program's whole interaction with the world goes through ports, which are declared in `main`'s header or as stored collections: files, sockets, clocks, devices, databases and the like. Foreign calls and logging go through ports too. Everything else is a pure value, so Zed needs no effect system. Reading a port gives you a value, and `<-` pushes one out. So a server, a batch job and a pipeline are all the same kind of thing: a function from input ports to output ports.

Runs repeat exactly, apart from a short list such as the order that messages arrive at a port and running out of a resource. Inputs and arrival order are recorded, so you can replay a failing run in a test.

### Timeouts and retries

`with timeout(d)`, `with retry(n, backoff: b)`, `with bound(n, overflow: policy)`

```zed
cache: Utf8String ->? [u8]
  with store(kv(endpoint))
  with timeout(0.2r with units("s"))
  with retry(2, backoff: #fixed(0.1r with units("s")));

hit = cache[key] else fetch(key);
```

Declaring a timeout changes the type. A read of `cache` is now `[u8] | #ioError | #timeout | #notFound`, and the program has to deal with that, here by treating anything other than a hit as a miss. `retry` adds no failure member, and the timeout covers all the attempts together. Pure code never times out, because a computation's finishing time isn't a value.

Retries, hedged requests, circuit breakers, rate limits and failover are declared on the port in the same way. The compiler permits retries only for operations declared safe to repeat, so a write that may already have landed needs an idempotence guarantee before it can be retried. Queues declare what happens when they are full (`#block`, `#dropOldest` or `#full`), so every queue has a limit, and by default a writer waits when it is full.

### Databases

`name: K ->? V with store(...)`

```zed
orders: OrderId ->? { total: rat, note: Utf8String | #none }
  with store(postgres(dbUrl, table: "orders", schema: sql("db/orders.sql")));

n = orders[id]?.note;     // Utf8String | #none | #notFound | #dbError
```

A stored table is a map like any other, and you read it with the same `[key]`. The compiler checks your declaration against the SQL schema at build time, without a live connection: a nullable column read as non-optional, or an unbounded string written to a `varchar(80)`, is a compile error at this line. At startup, the program compares the columns it uses with the real database. On a port that supports transactions, such as Postgres, writes made in one step of the program form one transaction, and you never write `begin` or `commit`.

### Incremental updates

`@memoized`

```zed
// sales is keyed by SaleId; each sale has a region and an amount.
@memoized
report = sales
  .group(s -> s.region)
  .map(rows -> rows.map(s -> s.amount).sum);
```

Incremental updates need no annotation. `@memoized` makes the build fail if this value isn't kept for reuse. When an input changes, the change goes through the same graph as a new batch of values (a *wave*), and only what it affects is recomputed. Changing one sale's amount updates its region's total, and moving a sale to another region updates both. The update stops wherever nothing downstream can see a difference. Spreadsheets, build systems and reactive user interfaces each build this by hand. In Zed it needs no extra code, and an incremental result always equals what a full recomputation would give.

This also powers live editing: a change to your source code is one more wave on one more port, so a running program can pick up the edit without a restart. If the edit changes the type of stored state, you supply a migration to the new type.

## Checks at compile time

### Ranges and refinements

`int[lo..=hi]`, `x.refine(p)`, `@ensure`

```zed
struct Span { lo: int, hi: int[lo..] }

width(positional s: Span) = s.hi - s.lo;   // inferred: int[0..]
// bad = Span(lo: 3, hi: 1);               // ✗ rejected: hi must be at least lo

@ensure odd(positional x) = (x * 2 + 1).refine(v -> v < 100);
                                           // inferred: x <= 49
a = odd(12);
// b = odd(60);                            // ✗ rejected: 60 > 49
```

Types can carry ranges and relations between fields, and the compiler tracks them through arithmetic without any annotations from you. That is how it removes bounds checks and picks the smallest machine representation. `refine` checks a condition at run time, giving `#invalid` if it fails. `@ensure` forbids that check: the compiler has to push the condition back onto the inputs and reject any caller it can't prove safe, so the check moves to compile time.

A field's range may name another field. The compiler reasons about such bounds with linear arithmetic, and no SMT solver is involved. The checks come from a small set of decidable procedures, so the compile time is predictable and the error message says exactly what stopped the proof.

### Units and taint

`with units("...")`, `with taint(#label)`

```zed
v = 3.0 with units("m/s");
t = 2.0 with units("s");
d = v * t;                 // has units "m"
// e = v + t;              // ✗ rejected: m/s + s

render: (Utf8String with taint(#clean)) -> Html;
comment = input with taint(#userInput);

// page = render("<p>" ++ comment ++ "</p>");   // ✗ rejected: user input reaches render
page = render("<p>" ++ escapeHtml(comment) ++ "</p>");
```

These are *facets*: extra facts about a value, tracked through every operation at compile time. Units and taint have no run-time cost. Units catch physics mistakes. Taint follows untrusted input through your program. Here `render` declares that it takes only clean text and `escapeHtml` is the function that removes the taint, so passing user input straight through is a type error. Any program can define a facet of its own in the same way, such as a latency or a parity.

### Cost

`f::cost`, `@cost(b)`, `@fused`, `@noalloc`

```zed
@cost(xs::len)
@fused
sumSquares(positional xs: [f64]) = xs.map(x -> x * x) >< (+);

@cost(xs::len * log(xs::len))
ranked(positional xs: [int]) = xs.sort(desc x -> x);

@noalloc
lerp(positional a: f64, positional b: f64, positional t: f64) = a * (1.0 - t) + b * t;
```

Every function has a computed upper bound on its work and its parallel depth, which you can read as `f::cost` and `f::depth`. Where no bound can be proved, they say `#unbounded`. Annotations like these are assertions about the plan the compiler chose: `@cost` states a bound, `@fused` says no intermediate collection is built, and `@noalloc` says the code uses no memory beyond registers. If one is false, the build fails. A performance requirement can be part of the code, and a change that breaks it fails the build.

## Code that runs at build time

### Partial evaluation

Any expression with known inputs.

```zed
struct User { id: int, name: Utf8String }

ok: User | #parseError(pos: int, msg: Utf8String) = Json.decode("{\"id\": 5, \"name\": \"John\"}");
// the constant User(id: 5, name: "John")

bad: User | #parseError(pos: int, msg: Utf8String) = Json.decode("{\"id\": \"five\"}");
// the constant #parseError(pos: 7, msg: "expected int for field 'id', got string")
```

Zed has no macro language and no `comptime` keyword. An expression your program needs, whose inputs are known at build time, is evaluated at build time, by the same evaluator with the same meaning. The JSON decoder above is ordinary Zed. Given a literal, the whole call runs during the build. Given a value only known at run time, the decoder is specialized to `User`, with the generic field lookups already gone. A regular expression known at build time compiles to a matcher in the same way, with nothing left to interpret. If a program does arrive at run time as data, `compile` turns it into a function using the same machinery.

### Reflection

`T::fields`, `T::shape`, `T::values`, `x::constraints`, `f::source`

```zed
type Size = #small | #medium | #large;

sizes = Size::values;       // {#large, #medium, #small}: atoms sort by name
names = User::fields;       // the fields of User, by name and type
```

Generic code can look at a type's structure. That's how `Json.decode` knows what `User` looks like, and every read is answered at build time, so reflection has no run-time cost.

### Grammars

`struct Name grammar { ... }`, `type T = Utf8String matching grammar { ... }`, `T.parse(s)`, `x.serialize`

```zed
struct Vec3 grammar { "(" x: f64 "," y: f64 "," z: f64 ")" }

v = Vec3.parse("(1.0, 2.0, 3.0)") else Vec3(x: 0.0, y: 0.0, z: 0.0);
s = v.serialize;       // "(1.0,2.0,3.0)"
```

Add `grammar` to a struct and its fields become a parser and a serializer for that format. You get one definition for both directions, so the two can't drift apart, and the compiler checks that the round trip gives you back the value. Grammars can be recursive, and the result is ordinary typed data. Here is a calculator, parser and evaluator together:

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

Binary formats work the same way, with the layout given by `bits`, `endian` and `length`. This is the layout of a PNG chunk:

```zed
struct Chunk grammar {
  n: int with bits(32) with endian(#big)
  kind: u8* with length(4)
  data: u8* with length(n)
  crc: int with bits(32) with endian(#big)
}
```

### Symbolic math

`f::source`, `expand(e)`, `derivative(e)`

```zed
p = ((x: rat) -> (x + 1r) ** 2)::source;
e = expand(p);          // x ** 2 + 2r * x + 1r
d = derivative(p);      // 2r * x + 2r
```

The source of a function is a value you can read, and rewriting it is an ordinary program. Each rewrite carries a reason that the compiler's proof checker validates, and the types of the binders are the assumptions, so `(x * y) div y` simplifies to `x` only when `y` is known to be at least 1. `compile` turns the result back into a function.

## Tests, laws and proofs

### Tests next to the code

`f(...) = ... test { input -> output, ... }`

```zed
double(positional x) = x * 2 test { 0 -> 0, 2 -> 4, -3 -> -6 }
```

Tests live on the definition and run at build time. With `@exhaustive` on a function over a small finite domain, every input is run.

### Laws

`law name(x: T) = expression;`

```zed
law doubleIsSum(x: int) = double(x) == x + x;
law addComm(a: int, b: int) = a + b == b + a;
law sortTwice(xs: [int]) = xs.sort(asc x -> x).sort(asc x -> x) == xs.sort(asc x -> x);
```

A law is a claim about your code. The compiler tries to prove it with a fixed ladder of methods. For a small domain it checks every case, and otherwise it tries the rewrites and decision procedures it has. If those fail, the law is tested on generated inputs. It then reports how far it got: exhaustively checked, proved, checked up to a bound, tested, assumed or unknown. An unproved law doesn't stop the build unless you ask it to with `@proved` or `--strict`.

The optimizer can use proved laws as rewrites. A `law` that was only tested is never used to rewrite your program. An `@associative` annotation that was only tested can still choose a fixed regrouping, and the report says so.

### Model checking

`loop` plus `law`

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

law neverBothGreen(j: Junction) = (j in reachable.R).implies(j.ns == #red || j.ew == #red);
```

A loop is a state machine, so the set of states it can reach is a fixpoint you can write in a few lines, and for a finite state space the compiler computes it at build time. Here `.image` collects a list's values into a set, the loop stops when `R` stops growing, and `reachable.R` is the final set. A `Junction` with both lights green is a legal value, but no sequence of commands reaches it, and the law checks exactly that. This covers the safety checks you would use a model checker like TLC for, in the language the system is written in. Liveness must be stated as a bound or a decreasing measure, and properties that rely on fairness can't be expressed. A failed check reports the sequence of steps that reached the bad state, as a value you can replay.

## Under the hood

### Error messages

Every error gives the rule that failed and the checker's whole chain of reasoning: each constraint, where it came from and how it reached this line. When the compiler has concrete evidence, such as two keys that collide or a value no `match` arm covers, it shows it. When a proof is missing, it names the expression or region it couldn't resolve. It then lists the repairs that would work, as in the [remap error](#remapping) above. The rules that reject a program are fixed lists, so whether a program is accepted never depends on how strong the optimizer is.

### Calling C, and being called from C

`@foreign("lib", "symbol")`, `@export("c", "symbol")`, `@stateless`

```zed
@foreign("m", "cbrt") @stateless cbrt: (positional x: f64) -> f64;

root = cbrt(8.0) else 0.0;

@export("c", "zed_score")
score(positional a: f64, positional b: f64) = a * 0.7 + b * 0.3;
```

A foreign call is an operation on a port. The declared `-> f64` is the C result, and the call also has a failure type, which is why `root` has an `else`. It takes the same `timeout` word as any other port, and `retry` if the function is marked `@stateless`, a promise about the library that the compiler can't check. Foreign structs declare their memory layout field by field, and C memory is read in place through that layout. `@export` compiles a function into a shared library with a generated C header. On the LLVM back end, C code compiled by Clang can be inlined into Zed code and optimized along with it.

### Memory

Memory has no syntax. Zed has no garbage collector, and there are no lifetimes or ownership annotations. Zed values can't form cycles, so exact reference counting is enough, and the compiler removes most of it: where a last use is known statically, the free is simply placed there, with no count at all. A functional update of a value nothing else refers to happens in place. Cyclic data lives in arenas or id-indexed graphs, where a stale lookup gives `#notFound` and not a dangling pointer. Freeing is spread out across the scheduler's work, so there are no tracing pauses and no long chains of frees. `@noalloc` and `@preallocated` let you assert a bounded footprint and have the build fail if it doesn't hold.

### Parallelism and determinism

There is no syntax for this either. Any two parts of a program with no dependency between them may run at once, so the compiler chooses where to split the work, using the dependency graph and the laws of each operator. The rule is that outputs are bit-identical at any core count, floating-point reductions included. The exceptions are a short, enumerated list: arrival order at ports, the interleaving at an output port that declares one, foreign-call order the program leaves open, `unordered` reductions, and running out of a resource. There is no undefined behavior, except where a foreign library breaks a promise made about it.

### Targets

One intermediate representation sits under everything. Back ends compile it to native multicore code through MLIR and LLVM, and to WebAssembly, GPUs, distributed dataflow (where the keys of your data double as partition keys), hardware synthesis and microcontrollers. The compiler is written in Zed itself, on top of a small kernel. A program that needs a port its target doesn't have is rejected at build time, and the error names the port and how the program reached it.

## License

Zed is released under the [MIT License](LICENSE).
