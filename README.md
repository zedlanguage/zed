> [!NOTE]
> **Zed is still under construction and is not yet ready for use, but it is coming soon.**
> Releases will be announced at [x.com/zedlang](https://x.com/zedlang). This page describes the language as it will be when finished.

<p align="center">
  <img src="docs/assets/banner.svg" alt="Zed" width="512">
</p>

Zed is a programming language that looks like ordinary code, but has no variables you overwrite and no statement order you have to get right. A Zed program is a set of definitions: each value says what it depends on, and the compiler works out the rest. Because the compiler can see that whole graph of dependencies, it can run your code in parallel, free memory without a garbage collector, recompute only what changed when an input changes, and reject many bugs before the program runs.

Here is a complete program. It counts the words in a file and prints them, most common first.

```zed
main(fs: Files) -> (stdout: Lines) {
  text = fs["input.txt"] else "";
  counts = text.split(" ").group(w -> w.lower).count;
  lines = counts as (w -> n) into (desc n -> w -> "${w}: ${n}");
  stdout <- lines.rank;
}
```

Nothing in it mentions threads, locks or allocation, yet the grouping runs on all your cores. The output is the same, bit for bit, on one core or on sixty-four. A missing file can't crash the program either: the type of `fs["input.txt"]` says the read can fail, and the `else` says what to do when it does. Delete the `else` and the program no longer compiles.

The rest of this page is a tour of the language. Each stop shows a piece of syntax, an example, and what the example means.

- [The basics](#the-basics): bindings, functions, numbers, strings, structs, unions, methods
- [Failure is a value](#failure-is-a-value)
- [Collections](#collections): maps, grouping, remapping, reducing, joins
- [Time and repetition](#time-and-repetition): recurrences, loops, history, laziness
- [The outside world](#the-outside-world): ports, streams, retries, databases, incremental updates
- [Checks at compile time](#checks-at-compile-time): ranges, units, taint, cost
- [Code that runs at build time](#code-that-runs-at-build-time): grammars, reflection, symbolic math
- [Tests, laws and proofs](#tests-laws-and-proofs)
- [Under the hood](#under-the-hood): modules, interfaces, C, memory, targets, error messages

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

Parameters are passed by name unless you mark them `positional`, so a call site says what its arguments mean. Any function can be called with a dot, so `5.double` is `double(5)`, and pipelines read left to right. A `...` in a call leaves the remaining named parameters open and gives you back a function. Parameter types can usually be left out: `double` works on any type with `*` and an integer literal, and the compiler infers that.

### Numbers

`42`, `1.5`, `3r`, `a / b`, `a div b`, `f64(n)`

```zed
big = 2 ** 100;              // no overflow; this is the exact integer
third = 1r / 3r;             // an exact rational
half = 1.0 / 2.0;            // f64
q = 7 div 2;                 // 3
ratio = f64(q) / 2.0;        // conversions are written out
```

An `int` is a mathematical integer. It can't overflow, because the compiler picks its machine representation from the range it can prove, and that is a plain machine word wherever a word is enough. `/` works on fractional types, and integers divide with `div` and `mod`. `r` marks an exact rational, so `0.1r + 0.2r == 0.3r` is true. Zed never converts a number for you: mixing `int` and `f64` is a compile error until you write `f64(n)`.

### Strings

`"text"`, `"${expression}"`, `a ++ b`

```zed
name = "Zed";
line = "total: ${2 + 3}";            // "total: 5"
title = "never" ++ "the" ++ "less";
```

String literals are UTF-8. Encodings are separate types (`U8String`, `Utf8String`, `Utf16String`, `Utf32String`), and you pick what you index by, such as code points or bytes, through a named view like `text::codepoints`. `++` builds a rope in O(1), so joining strings in a loop doesn't go quadratic.

### Structs

`struct Name { field: type, field: type = default }`, `Name(field: value)`, `x with { field = value }`

```zed
struct Point { x: f64, y: f64 }
struct Circle { center: Point, radius: f64 = 1.0 }

p = Point(x: 1.0, y: 2.0);
moved = p with { x = 3.0 };
unit = Circle(center: p);
```

Constructors take their arguments by name. `with` makes a copy with some fields changed, and when the compiler can see the original isn't used again, the copy is an update in place with no allocation. Structs compare by value. There are no classes, no inheritance and no object identity.

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

An atom is a constant that is its own name, with no declaration needed. A union says a value is one of several things. A `match` must cover every case: leave out an arm and the compiler rejects the program and shows you a value that no arm handles. An arm that can never run is also rejected.

### Methods and the next value

`Type.method() { field' = ...; }`, `x.method()`, `x*.method()`

```zed
struct Counter { n: int, peak: int }

Counter.bump(positional by) -> int {
  n' = n + by;
  peak' = max(peak, n + by);
  return n;
}

Counter.atPeak = n == peak;

start = Counter(n: 0, peak: 0);
after, was = start.bump(2);
```

A method is a function with an implicit first parameter whose fields are in scope. `n'` means "the value of `n` in the next version of this struct". The method doesn't change `start`: it returns a new `Counter` and its declared result, and you have to take both. The one way to write something that looks like mutation is a `*` in a loop body, as in `prev = c*.bump(3);`, which replaces `c` in the loop's next step. So no call changes anything unless the text shows a `*`.

## Failure is a value

### `else` and `?.`

`T | #someFailure`, `x else fallback`, `x?.field`

```zed
parse: (Utf8String) -> Config | #syntaxError(pos: int);

conf = parse(text) else defaultConfig;
port = parse(text)?.server?.port else 8080;
```

There are no exceptions and no null. A function that can fail says so in its return type, by returning a union with an atom in it. `else` replaces any failure with a fallback, and `?.` reads a field if there is one and passes the failure along if there isn't. You can't use a `Config | #syntaxError` where a `Config` is needed, so it isn't possible to forget the error case.

The compiler also adds failures only where they can really happen. `a div b` has type `int` when `b` can be shown never to be zero, and `int | #divByZero` when it can't. `xs[i]` is plain `T` when `i` is known to be in range. Prove the bound, and the failure and its run-time check both disappear.

### Failures in a pipeline

`r is T`, `r is not T`

```zed
results = files.map(f -> read(f)).map(b -> parse(b));

good = results.where(r -> r is Config);
bad = results.where(r -> r is not Config);
```

One bad file doesn't stop the run. A failure is an ordinary value, sitting in the collection next to the successes under the same key, so you can split them, count them or report them. Each one also carries where it came from (which file, which offset, which step), so you don't have to thread that information through by hand.

What you can't do is ignore them by accident:

```zed
amounts = files.map(f -> int(read(f)));
sum = amounts >< (+);                     // ✗ rejected: some amounts may be failures
```

You say what you mean instead:

```zed
sum1 = amounts.where(a -> a is int) >< (+);     // skip the failures
sum2 = amounts.map(a -> a else 0) >< (+);       // count them as zero
```

## Collections

### Everything is a map

`[a, b, c]`, `{ k -> v }`, `{ a, b }`, `m[k]`

```zed
xs = [3, 1, 4, 1, 5];                  // int[0..<5] -> int
ages = { "Ann" -> 36, "Bob" -> 41 };   // Utf8String -> int
tags = { #red, #green };               // a set: a map from each member to itself

first = xs[0];                         // 3: the index is known to be in range
ann = ages["Ann"];
carol = ages["Carol"] else 0;

big = xs.map(x -> x * 10).where(x -> x > 20).sort(desc x -> x);
```

An array is a map whose keys are `0..<n`, a set is a map from each key to itself, a struct is a map from field names to values, and a function is a map too. So `xs[i]`, `f(x)` and `p.x` are the same idea, and one set of tools works on all of them. Nested maps are the normal way to hold tables: `Region -> Product -> rat` is a table of sales by region and product, stored in whichever layout suits the code that reads it.

### Grouping

`m.group(x -> key)`, `m.rekey(x -> key)`

```zed
byCity = users.group(u -> u.city);      // City -> UserId -> User
byId = users.rekey(u -> u.id);          // ✗ rejected unless id is known to be unique
```

`group` adds a level, so nothing can be lost. `rekey` replaces the key, and that can make two entries land on one key, so the compiler demands evidence that the new key is unique, such as a declared key or a function it can see never collides. It rejects anything else and shows you the two entries that would collide. No value ever silently overwrites another in Zed.

### Remapping

`m as (pattern) into (pattern)`

```zed
transposed = matrix as (r -> c -> v) into (c -> r -> v);
ranking = scores as (name -> s) into (desc s -> name -> s);
```

`as ... into ...` is a small picture of the shape you have and the shape you want. It is the second, more concise way of writing what `group`, `rekey` and `sort` do, and both forms compile to the same thing. In the second line, putting `desc s` in key position sorts by score, and keeping `name` as a level below it means that two people with the same score can't collide. A remap can move keys around, add levels or drop whole entries, but it can't overwrite a value. If you ask it to, you get an error that lists the ways out:

```text
error: this remap would map one key to many values
  the `(k1, k2)` keypaths collapse onto `k1`, but their values survive.
  drop the values too:         into (k1 -> k2 -> _)         -- truncate to a set-leaf
  or keep the discriminator:   into (k1 -> k2 -> v)         -- the residue written back (widen it if it must move)
  or say how the values merge: into (k1 -> k2 >< op -> v)   -- explicit reduction; owes op's Boom obligations
```

### Reducing

`m >< op`, `m >< op else fallback`, `(pattern >< op -> value)`, `m.foldl(init, op)`

```zed
total = readings >< (+);
longest = words.map(w -> w.len) >< max else 0;
pivot = sales as (i -> s) into (s.region -> s.product -> i >< (+) -> s.amount);
```

`><` is the only construct that merges values. It runs in parallel, so it needs an operator that is safe to regroup: `+` and `max` are known to be, and for your own operators you state the law.

```zed
struct Moments { n: int, sum: rat }

@associative @commutative
combine(positional a: Moments, positional b: Moments) =
  Moments(n: a.n + b.n, sum: a.sum + b.sum);

m = xs.map(x -> Moments(n: 1, sum: x)) >< combine else Moments(n: 0, sum: 0r);
```

The compiler tests or proves an annotation like `@associative`. If an operator isn't associative, you say which way to fold with `foldl` or `foldr`, and that's fine too. A reduction over nothing can't be silently wrong: the `else` gives the answer for an empty collection, and without it the result type includes `#empty`, unless the operator has an identity. The `pivot` line builds the whole sales table in one expression, with a level for region, a level for product, and the amounts summed.

Floating-point sums get special care. `samples >< (+)` computes the exact sum and rounds it once, so the result doesn't depend on how the work was split or how many cores ran it. If you'd rather have speed than that guarantee, you ask for it, and it shows in the type: `samples >< (+) unordered`.

### Joins

`a.join(b, on: #field, kind: #left)`, `a.diff(b, on: #field)`, `for x in a, y in b where ...`

```zed
paid = orders.join(payments, on: #orderId, kind: #left);
// OrderId -> (Order, Payment | #none)

unpaid = orders.diff(payments, on: #orderId);

shipped = for o in orders, s in shipments where o.orderId == s.orderId { (o, s) };
pairs = for i in 0..<n, j in i+1..<n { (i, j) };
```

A missing match in a left join is the atom `#none`, which the type shows, and not a row of nulls. A `for` over several collections is a join as well, and the compiler can pick a hash join or a merge join for it instead of two nested loops. Queries and loops aren't two separate worlds here: they compile to the same terms and are optimized together.

## Time and repetition

### Recurrences

`x[i] = f(x[i-1]) with x[-1] = start;`

```zed
cdf[i] = cdf[i-1] + hist[i] with cdf[-1] = 0;

d[i][j] = min(d[i-1][j] + 1, d[i][j-1] + 1, d[i-1][j-1] + cost(a[i], b[j]))
  with d[-1][j in -1..<b::len] = j + 1, d[i in 0..][-1] = i + 1;
```

You write the equation and the boundary cases, as you would on a whiteboard. The first line is a running total. The second is edit distance, and it needs no explicit table and no choice of memoization or fill order. The compiler reads the dependencies and picks a plan: it fills the table wave by wave across your cores if you need most of it, and memoizes on demand if you only touch part of it.

The algebra of the recurrence matters too. Some loops that look serial can be run in parallel, because the compiler recognizes them:

```zed
cur[i] = max(xs[i], cur[i-1] + xs[i]) with cur[-1] = 0;
best = cur >< max else 0;

state[i] = csvStep(state[i-1], text::codepoints[i]) with state[-1] = #outsideQuotes;
```

The first recurrence is maximum subarray, whose step is affine over max and plus, so it runs as a parallel scan. The second walks a CSV file with a small state machine. Because the states are finite, the compiler can tabulate the transitions, and tables compose in any grouping, so a job that every other tool does one byte at a time splits across cores.

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

A loop describes one step: `pos'` is the next value of `pos`, written in terms of the current values. Both updates here read the old `pos`, so they don't race and their order doesn't matter. A data race can't even be written. After the loop, `sim.pos` is the final value.

`sim::frames` is every step of the run, kept only if you read it. If you don't, the compiler keeps just the two slots it needs. If you do, you've got time travel for free. This is how you write undo:

```zed
run = loop t {
  while t < edits::len;
  doc' = doc.patch(edits[t]) with doc = empty;
};

previous = run::frames[run::len - 2].doc else empty;
```

The versions share structure, so reading an old one is cheap and keeping them all doesn't copy the document each time.

### Only what's needed runs

`for i in n.. { ... }`, unused fields, `.first`

```zed
stats(positional data: [f64]) {
  n = f64(data::len);
  mean = data.sum / n;
  sd = (data.map(x -> (x - mean) ** 2).sum / n).sqrt;
  return { mean:, sd: };
}

m = stats(xs).mean;      // sd is never computed

firstPrime = (for i in n.. { i }).where(isPrime).first;
```

Work runs only if a result depends on it. A caller that reads `.mean` doesn't pay for `sd`, and you don't need two versions of the function or a flag. Zed isn't lazy in the Haskell sense, though, and there are no thunks to pile up: the compiler decides at build time what to compute eagerly and what on demand. The `firstPrime` search runs over an unbounded range. Candidates are tried in parallel, and the ones that can't win are canceled once a smaller prime is found.

## The outside world

### Ports

`main(input: T) -> (output: U) { output <- value; }`

```zed
main(req: Stream(Query)) -> (resp: Stream(Answer)) {
  resp <- req.map(q -> lookup(db, q) else #unknown);
}
```

A program's whole interaction with the world goes through ports, which are listed in `main`'s header: files, sockets, clocks, devices and the like. Everything else is a pure value, and there is no effect system to learn, because there is nothing else that could have an effect. Reading a port gives you a value, and `<-` pushes one out. So a server, a batch job and a pipeline are all the same kind of thing: a function from input ports to output ports.

Runs repeat exactly, apart from a short, explicit list of things like the order that messages arrive at a port, and those are recorded, so you can replay a failing run in a test.

### Timeouts and retries

`with timeout(d)`, `with retry(n, backoff: b)`, `with bound(n, overflow: policy)`

```zed
cache: Utf8String ->? [u8] with store(kv(endpoint)) with timeout(200 with units("ms"));

hit = cache[key] else fetch(key);
```

Declaring a timeout changes the type. A read of `cache` is now `[u8] | #ioError | #timeout | #notFound`, and the program has to deal with that, here by treating anything other than a hit as a miss. Pure code never times out, because a computation's finishing time isn't a value.

Retries, hedged requests, circuit breakers, rate limits and failover are declared on the port in the same way. The compiler won't let you retry an operation that isn't safe to repeat, such as a write that might already have landed. Queues declare what happens when they are full (`#block`, `#dropOldest` or `#full`), so unbounded growth can't happen by default.

### Databases

`name: K ->? V with store(...)`

```zed
orders: OrderId ->? { total: rat, note: Utf8String | #none }
  with store(postgres(dbUrl, table: "orders", schema: sql("db/orders.sql")));

n = orders[id]?.note;     // Utf8String | #none | #notFound | #dbError
```

A stored table is a map like any other, and you read it with the same `[key]`. The compiler checks your declaration against the SQL schema at build time, without a live connection: a nullable column read as non-optional, or an unbounded string written to a `varchar(80)`, is a compile error at this line. At startup, the program compares the columns it uses with the real database. Writes made in one step of the program form one transaction, and you never write `begin` or `commit`.

### Incremental updates

`@memoized`

```zed
@memoized
report = sales
  .join(costs, on: #sku)
  .group(((s, c)) -> s.region)
  .map(rows -> rows.map(((s, c)) -> margin(s, c)).sum);
```

When an input changes, the program handles the change as a new wave of values through the same graph, and recomputes only what the change affects. A change to one sale updates one region's total. If a recomputed value comes out the same, the update stops there. Spreadsheets, build systems and reactive user interfaces all need this, and they each build it by hand. In Zed it's the same machinery as everything else, and an incremental result always equals what a full recomputation would have given.

This also powers live editing: a change to your source code is one more wave on one more port, so a running program can pick up the edit without a restart.

## Checks at compile time

### Ranges and refinements

`int[lo..=hi]`, `x.refine(p)`, `@ensure`

```zed
struct Span { lo: int, hi: int[lo..] }

s = Span(lo: 2, hi: 5);
width = s.hi - s.lo;                // inferred: int[0..]

@ensure odd(positional x) = (x * 2 + 1).refine(v -> v < 100);
                                    // inferred: x <= 49
a = odd(12);
b = odd(60);                        // ✗ rejected: 60 > 49
```

Types can carry ranges and relations between fields, and the compiler tracks them through arithmetic without any annotations from you. That is how it removes bounds checks and picks the smallest machine representation. `refine` checks a condition at run time, giving `#invalid` if it fails. `@ensure` forbids that check: the compiler has to push the condition back onto the inputs and reject any caller it can't prove safe, so the check moves to compile time.

There are no dependent types and no SMT solver in this. The checks come from a small set of decidable procedures, so the compile time is predictable and the error message says exactly what stopped the proof.

### Units and taint

`with units("...")`, `with taint(#label)`

```zed
v = 3.0 with units("m/s");
t = 2.0 with units("s");
d = v * t;                 // has units "m"
e = v + t;                 // ✗ rejected: m/s + s

rows = exec(db, "SELECT * WHERE name = " ++ userName);            // ✗ rejected
rows = exec(db, "SELECT * WHERE name = " ++ sanitize(userName));  // accepted
```

These are *facets*: extra facts about a value, tracked through every operation at compile time and erased from the compiled code. Units catch physics mistakes. Taint follows untrusted input through your program, and a database's `exec` declares that it takes only clean text, so an SQL injection is a type error. Any program can define a facet of its own in the same way, such as a latency or a parity.

### Cost

`f::cost`, `@cost(b)`, `@noalloc`, `@fused`

```zed
@cost(n * log(n))
@noalloc
sortedTop(positional xs: [int]) = xs.sort(desc x -> x);
```

Every function has a computed upper bound on its work and its parallel depth, which you can read as `f::cost` and `f::depth`. Annotations like `@cost`, `@noalloc` and `@fused` are assertions about the plan the compiler chose. If one is false, the build fails. It doesn't silently get slower. A performance requirement can be part of the code, and a change that breaks it is caught in review, not in production.

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

There's no separate macro language, no `comptime` keyword and no code generator. Whatever can be computed from what is known at build time is computed at build time, by the same evaluator with the same meaning. The JSON decoder above is ordinary Zed. Given a literal, the whole call runs during the build. Given a value only known at run time, the decoder is specialized to `User`, with the generic field lookups already gone. A regular expression known at build time compiles to a matcher in the same way, with nothing left to interpret. If a program does arrive at run time as data, `compile` turns it into a function using the same machinery.

### Reflection

`T::fields`, `T::shape`, `T::values`, `x::constraints`, `f::source`

```zed
type Size = #small | #medium | #large;

sizes = Size::values;       // {#small, #medium, #large}
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
struct Prod grammar { factors: Atom sep "*" }
struct Paren grammar { "(" inner: Sum ")" }
type Number = Utf8String matching grammar { digit digit* };
type Atom = Number | Paren;

Sum.eval = terms.map(t -> t.eval).sum;
Prod.eval = factors.map(f -> f.eval) >< (*);
Paren.eval = inner.eval;
Number.eval = int(this) else 0;

value = Sum.parse("2*(3+4)")?.eval;     // 14, or #syntaxError
```

Binary formats work the same way, with the layout given by `bits`, `endian` and `length`:

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

Proved laws aren't just documentation, because the optimizer can use them as rewrites. A law that was only tested licenses nothing, so it can never make your program wrong.

### Model checking

`loop` plus `law`

```zed
type Cmd = #tick | #fault;

advance(positional l: Light, positional c: Cmd) =
  if c == #fault { #red } else { next(l) };

reachable = loop {
  R' = R.union(R.flatMap(l -> [advance(l, #tick), advance(l, #fault)]).image) with R = { #red };
};

law faultStops(l: Light) = (l in reachable.R).implies(advance(l, #fault) == #red);
```

A loop is a state machine, so the set of states it can reach is a fixpoint you can write in a few lines, and for a finite state space the compiler computes it at build time. There's no separate specification language: this is what TLA+ gives you, written in the language the system is written in. A failed check reports the sequence of steps that reached the bad state, as a value you can replay.

## Under the hood

### Modules

`import a.b;`, `import a.b as c;`, `import a.b.{x, y};`, `local`

```zed
import geometry.shapes.{Point, dist};

far = dist(Point(x: 0.0, y: 0.0), Point(x: 3.0, y: 4.0));
```

A file is a module. Everything in it is exported unless marked `local`, and there are no wildcard imports, so you can always tell by reading where a name came from. An import can be pinned to the content hash of what it refers to with `@hash`.

### Generics and interfaces

`type Name(T) = ...`, `interface Name { ... }`

```zed
type Stack(T) = [T];
push(s: Stack(T), x: T) = s ++ [x];
top(s: Stack(T)) = s.last;                 // T | #none

interface Named { name: Utf8String }
hello(positional n: Named) = "Hi, ${n.name}";
```

A capitalized free name in a signature is a type variable, with nothing to declare. Interfaces are structural: any value with a `name` fits `Named`, with no `implements` clause. An interface can also hold laws, so the algebra that `><` relies on, from `Monoid` to `CommRing`, is ordinary library code.

### Calling C, and being called from C

`@foreign("lib", "symbol")`, `@export("c", "symbol")`, `@stateless`

```zed
@foreign("m", "cbrt") @stateless cbrt: (x: f64) -> f64;

@export("c", "zed_score")
score(positional a: f64, positional b: f64) = a * 0.7 + b * 0.3;
```

A foreign call is an operation on a port, so it has a failure type and takes the same `timeout` and `retry` words as any other port. Foreign structs declare their memory layout field by field, and C memory is read in place through that layout. `@export` compiles a function into a shared library with a generated C header. On the LLVM back end, C code compiled by Clang can be inlined into Zed code and optimized along with it.

### Memory

There is no syntax for memory, and that's the point. Zed has no garbage collector, and there are no lifetimes or ownership annotations. Zed values can't form cycles, so exact reference counting is enough, and the compiler removes most of it: where a last use is known statically, the free is simply placed there, with no count at all. A functional update of a value nothing else refers to happens in place. Cyclic data lives in arenas or id-indexed graphs, where a stale lookup gives `#notFound` and not a dangling pointer. Freeing is spread out across the scheduler's work, so there are no pauses. `@noalloc` and `@preallocated` let you assert a bounded footprint and have the build fail if it doesn't hold.

### Parallelism and determinism

There is no syntax for this either. Any two parts of a program with no dependency between them may run at once, so the compiler chooses where to split the work, using the dependency graph and the laws of each operator. The rule is that outputs are bit-identical at any core count, floating-point reductions included. The exceptions are a short, enumerated list (arrival order at ports, `unordered` reductions, and a few others), each visible in the program's text. There is no undefined behavior, except where a foreign library breaks a promise made about it.

### Targets

One intermediate representation sits under everything. The first back ends compile through MLIR and LLVM to native x86-64, and the compiler is written in Zed itself, on top of a small kernel. The design also covers WebAssembly, GPUs, distributed dataflow (where the keys of your data double as partition keys), hardware synthesis and microcontrollers. A program that needs a port its target doesn't have is rejected at build time, and the error names the port and how the program reached it.

### Error messages

A rejection is meant to teach you the fix. Every error gives the concrete evidence (the two keys that collide, or a value that no `match` arm covers), and the checker's whole chain of reasoning: each constraint, where it came from and how it reached this line. It then lists the repairs that would work, as in the [remap error](#remapping) above. Because the rules that reject programs are closed lists, not heuristics, a program's acceptance never depends on how strong the optimizer happens to be.

## Why Zed exists

Many systems recover a value graph after the fact, because it's what makes their job possible. Spreadsheets, SSA form in compilers, Spark, build systems, reactive UI frameworks and out-of-order CPUs all do this, each from scratch, by working backward from code or configuration. Zed's bet is that the graph should be the program. Then parallel scheduling, memory management, incremental updates and many correctness checks stop being separate tools with separate models, and become things one compiler reads from one structure.

The other bet is that you shouldn't pay for this in ceremony. The word-count program at the top is about as short as it would be in Python. It still runs in parallel, has no way to crash on a missing file, and gives the same answer every time.
