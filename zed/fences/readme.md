<!-- The `zed` fences of README.md, copied by the sync tool: do not edit. -->

<!-- README.md:38 layer L7: ring L7, word L1 (Utf8String), label none; section [Step 1: the data] 1 -->
```zed
// region -> day -> sku -> quantity sold
sales: Utf8String ->? [Utf8String ->? int];

// sku -> price in dollars
prices: Utf8String ->? int;
```

<!-- README.md:94 layer L1: ring L1, word none, label none; section [Step 2: looking up a keypath] 1 -->
```zed
northOrZero = northPens else 0;
northPens = sales["North"][0]["pen"];
eastPens = sales["East"][0]["pen"];
```

<!-- README.md:135 layer L8: ring L8, word none, label none; section [Step 3: revenue per sale] 1 -->
```zed
revenue = sales as (region -> day -> sku -> q) into (region -> day -> sku -> q * prices[sku]);
```

<!-- README.md:163 layer L8: ring L8, word L3 (where), label none; section [Step 4: sales with no price] 1 -->
```zed
flat = revenue as (region -> day -> sku -> r) into ((region, day, sku) -> r);
unpriced = flat.where(r -> r is not int);
```

<!-- README.md:202 layer L1: ring L1, word none, label none; section [Step 5: daily totals] 1 -->
```zed
// daily = revenue as (region -> day -> sku -> r) into (region -> day -> r);   // ✗ Collision: two skus land on one keypath
```

<!-- README.md:270 layer L8: ring L8, word none, label none; section [Step 6: adding values that may be failures] 1 -->
```zed
dailyAll = revenue as (region -> day -> sku -> r) into (region -> day -> sku >< (+) -> r);
```

<!-- README.md:311 layer L8: ring L8, word none, label none; section [Step 6: adding values that may be failures] 2 -->
```zed
daily = revenue as (region -> day -> sku -> r) into (region -> day -> sku >< (+) -> (r else 0));
```

<!-- README.md:341 layer L3: ring L3, word none, label none; section [Step 7: totals per region] 1 -->
```zed
regionTotals = daily >< (+);
```

<!-- README.md:373 layer L8: ring L8, word L7 (reducer), label none; section [Step 8: units sold per product] 1 -->
```zed
lines = sales as (region -> day -> sku -> q) into ((region, day, sku) -> { sku:, q: });

sold: Utf8String ->? int with reducer((+));
for line in lines { sold[line.sku] <- line.q; };
```

<!-- README.md:420 layer L6: ring L6, word none, label none; section [Step 9: a running total] 1 -->
```zed
east = daily["East"] else [];
running[i] = running[i-1] + east[i] with running[-1] = 0;
```

<!-- README.md:453 layer L6: ring L6, word none, label none; section [Step 10: the change from the day before] 1 -->
```zed
trend = loop t {
  while t < east::len;
  prev' = east[t] with initial prev = 0;
  change' = east[t] - prev with initial change = 0;
};
```

<!-- README.md:488 layer L10: ring L10, word L3 (map), label none; section [Step 11: pens left on the shelf] 1 -->
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

<!-- README.md:557 layer L12: ring L7, word L12 (units), label none; section [Step 12: the mass of the shipment] 1 -->
```zed
penMass = 20 with units("g");          // one pen
crateMass = 1 with units("kg");        // the crate they ship in
shipped = (sold["pen"] else 0) * penMass;
// load = shipped + crateMass;         // ✗ Units that differ where an operation requires equal ones: g + kg
load = shipped + crateMass * (1000 with units("g/kg"));
```

<!-- README.md:587 layer L8: ring L8, word L1 (Utf8String), label none; section [Step 13: the whole calculation] 1 -->
```zed
regionTotals = daily >< (+);
daily = revenue as (region -> day -> sku -> r) into (region -> day -> sku >< (+) -> (r else 0));
revenue = sales as (region -> day -> sku -> q) into (region -> day -> sku -> q * prices[sku]);

sales: Utf8String ->? [Utf8String ->? int];
prices: Utf8String ->? int;
```

<!-- README.md:610 layer L8: ring L8, word L5 (orderedValues), label none; section [A complete program] 1 -->
```zed
main(fs: Files) -> (stdout: Lines) {
  text = fs["input.txt"] else "";
  counts = text.split(" ").group(w -> w.lower).count;
  lines = counts as (w -> n) into (desc n -> w -> "${w}: ${n}");
  stdout <- lines.orderedValues;
}
```

<!-- README.md:714 layer L10: ring L10, word none, label none; section [Bindings] 1 -->
```zed
total = price * quantity;
price = 12;
quantity = 3;
port: int[1..=65535] = 8080;   // an integer from 1 through 65535, both included
```

<!-- README.md:738 layer L10: ring L10, word L1 (Utf8String), label none; section [Functions] 1 -->
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

<!-- README.md:778 layer L1: ring L1, word none, label none; section [Numbers] 1 -->
```zed
big = 2^100;                // 2 to the power 100, the exact integer, with no overflow
third = 1r / 3r;             // an exact rational
half = f64(1) / 2.0;         // 2.0 takes the format of f64(1); 1.0 / 2.0 alone would be rejected, since nothing gives it a format
q = 7 div 2;                 // 3
ratio = f64(q) / 2.0;        // conversions are written out; 2.0 takes the format of f64(q)
twice(x: f64) = x * 2.0;     // 2.0 takes the format of x, and x * 2 would work too
// bad = q + 1.5;            // ✗ Numeric literal at a carrier that cannot take it: q is an int, and 1.5 is never an int
```

<!-- README.md:807 layer L3: ring L3, word none, label none; section [Strings] 1 -->
```zed
name = "Zed";
line = "total: ${2 + 3}";            // "total: 5"
title = "never" ++ "the" ++ "less";
z = name::codepoints[0];             // the first code point, a char32
```

<!-- README.md:829 layer L2: ring L2, word none, label none; section [Structs] 1 -->
```zed
struct Point { x: f64, y: f64 }
struct Circle { center: Point, radius: f64 = 1 }

p = Point(x: 1, y: 2);
moved = p with { x = 3 };
unit = Circle(center: p);

Point.norm = (x * x + y * y).sqrt;
size = p.norm;
```

<!-- README.md:859 layer L2: ring L2, word none, label none; section [Atoms, unions and match] 1 -->
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

<!-- README.md:896 layer L10: ring L10, word L5 (last), label none; section [Generics and interfaces] 1 -->
```zed
type Stack(T) = [T];
push(s: Stack(T), x: T) = s ++ [x];
top(s: Stack(T)) -> T | #none = s.last;

interface Named { name: Utf8String }
hello(positional n: Named) = "Hi, ${n.name}";
```

<!-- README.md:924 layer L2: ring L2, word none, label none; section [Modules] 1 -->
```zed
import geometry.shapes.{Point, dist};

far = dist(Point(x: 0, y: 0), Point(x: 3, y: 4));
```

<!-- README.md:948 layer L7: ring L7, word L1 (Utf8String), label none; section [`else` and `?.`] 1 -->
```zed
parse: (Utf8String) -> Config | #syntaxError(pos: int);

conf = parse(text) else defaultConfig;
port = parse(text)?.server?.port else 8080;
```

<!-- README.md:978 layer L3: ring L1, word L3 (where), label none; section [Failures in a pipeline] 1 -->
```zed
results = files.map(f -> read(f)).map(t -> parse(t));

good = results.where(r -> r is Config);
bad = results.where(r -> r is not Config);
```

<!-- README.md:1031 layer L3: ring L3, word L3 (map), label none; section [Failures in a pipeline] 2 -->
```zed
amounts = files.map(f -> int(read(f)));         // int(s) converts text to an int, and can fail
sumAll = amounts >< (+);                        // the sum, or all the failures: + never sees one
```

<!-- README.md:1038 layer L3: ring L3, word L3 (where), label none; section [Failures in a pipeline] 3 -->
```zed
sum1 = amounts.where(a -> a is int) >< (+);     // skip the failures
sum2 = amounts.map(a -> a else 0) >< (+);       // count them as zero
```

<!-- README.md:1066 layer L5: ring L5, word L5 (sort), label none; section [Everything is a map] 1 -->
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

<!-- README.md:1131 layer L4: ring L1, word L4 (group), label none; section [Grouping] 1 -->
```zed
// users : UserId -> User
byCity = users.group(u -> u.city);      // City ->? (UserId -> User)
// byId = users.rekey(u -> u.id);       // ✗ Collision: id is not known to be unique
```

<!-- README.md:1167 layer L8: ring L8, word none, label none; section [Remapping] 1 -->
```zed
transposed = matrix as (r -> c -> v) into (c -> r -> v);
ranking = scores as (name -> s) into (desc s -> name -> s);

// totals = sales as (region -> sku -> amount) into (region -> amount);   // ✗ Collision: two skus land on one region
totals = sales as (region -> sku -> amount) into (region -> sku >< (+) -> amount);
```

<!-- README.md:1262 layer L8: ring L8, word none, label none; section [Remapping] 2 -->
```zed
// revenue : region -> year -> sku -> amount
bySku = revenue as (region -> year -> sku -> amount) into (sku -> region -> year -> amount);
perYear = revenue as (region -> year -> sku -> amount) into (sku -> year -> region >< (+) -> amount);
years = revenue as (region -> year -> sku -> amount) into (region -> year -> _);

// bad = revenue as (region -> year -> sku -> amount) into (sku -> year -> amount);   // ✗ Collision: two regions land on one keypath
```

<!-- README.md:1362 layer L8: ring L8, word L3 (map), label none; section [Reducing] 1 -->
```zed
total = readings >< (+);
longest = words.map(w -> w.len) >< max else 0;
pivot = sales as (i -> s) into (s.region -> s.product -> i >< (+) -> s.amount);
```

<!-- README.md:1444 layer L16: ring L3, word L16 (@commutative), label none; section [Reducing] 2 -->
```zed
struct Moments { n: int, sum: rat }

@associative @commutative
combine(positional a: Moments, positional b: Moments) =
  Moments(n: a.n + b.n, sum: a.sum + b.sum);

// values : [rat]
m = values.map(x -> Moments(n: 1, sum: x)) >< combine else Moments(n: 0, sum: 0r);
```

<!-- README.md:1492 layer L7: ring L7, word L7 (reducer), label none; section [Pushing into a map] 1 -->
```zed
hist: int ->? int with reducer((+));
for w in words { hist[w.len] <- 1; };

same = words.group(w -> w.len).count;   // the same table, written as a pull
```

<!-- README.md:1560 layer L5: ring L5, word L5 (join), label none; section [Joins] 1 -->
```zed
// Both inputs are uniquely keyed by OrderId; orderId is their join key.
paid = orders.join(payments, on: #orderId, kind: #left);
// OrderId -> (Order, Payment | #none)

unpaid = orders.diff(payments, on: #orderId);

shipped = for o in orders, s in shipments where o.orderId == s.orderId { (o, s) };
pairs = for i in 0..<n, j in i+1..<n { (i, j) };
```

<!-- README.md:1651 layer L5: ring L1, word L5 (first), label none; section [Chunks] 1 -->
```zed
sessions = clicks.chunkBy(c -> c.userId).map(s -> Session(start: s.first.time, count: s.count));
```

<!-- README.md:1697 layer L14: ring L14, word L14 (matmul), label none; section [Vectors and matrices] 1 -->
```zed
scale(positional s: T, positional v: [T; n]) = s * v;     // result: [T; n]

a: [f64; 2, 3] = [[1, 2, 3], [4, 5, 6]];
b: [f64; 3, 2] = [[1, 0], [0, 1], [1, 1]];
c = a.matmul(b);                                          // [f64; 2, 2]
// d = a.matmul(a);                                       // ✗ Levels of one name with different domains: 3 columns, 2 rows
```

<!-- README.md:1736 layer L6: ring L6, word none, label none; section [Recurrences] 1 -->
```zed
running[i] = running[i-1] + xs[i] with running[-1] = 0;

d[i][j] = min(d[i-1][j] + 1, d[i][j-1] + 1, d[i-1][j-1] + cost(a[i], b[j]))
  with d[-1][j in -1..<b::len] = j + 1, d[i in 0..][-1] = i + 1;
```

<!-- README.md:1786 layer L6: ring L6, word none, label none; section [Recurrences] 2 -->
```zed
cur[i] = max(xs[i], cur[i-1] + xs[i]) with cur[-1] = 0;
best = cur >< max else 0;

state[i] = csvStep(state[i-1], text::codepoints[i]) with state[-1] = #outsideQuotes;
```

<!-- README.md:1846 layer L6: ring L6, word L6 (::frames), label none; section [Loops] 1 -->
```zed
sim = loop t {
  while t < maxSteps;
  pos' = pos + vel * dt with initial pos = p0;
  vel' = vel + accel(pos) * dt with initial vel = v0;
  until pos'.x > bound;
};

final = sim.pos;
history = sim::frames;
steps = sim::len;
```

<!-- README.md:1875 layer L6: ring L6, word L6 (::frames), label none; section [Loops] 2 -->
```zed
run = loop t {
  while t < edits::len;
  doc' = doc.patch(edits[t]) with initial doc = empty;
};

previous = run::frames[run::len - 2]?.doc else empty;
```

<!-- README.md:1912 layer L10: ring L10, word none, label none; section [Methods and the next value] 1 -->
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

<!-- README.md:1938 layer L5: ring L3, word L5 (first), label none; section [Only what's needed runs] 1 -->
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

<!-- README.md:1973 layer L7: ring L2, word L7 (Stream), label none; section [Ports] 1 -->
```zed
main(req: Stream(Query)) -> (resp: Stream(Answer)) {
  resp <- req.map(q -> answer(q));
}
```

<!-- README.md:1997 layer L21: ring L7, word L21 (store), label none; section [Timeouts and retries] 1 -->
```zed
cache: Utf8String ->? [u8]
  with store(kv(endpoint))
  with timeout(0.2r with units("s"))
  with retry(2, backoff: #fixed(0.1r with units("s")));

hit = cache[key] else fetch(key);
```

<!-- README.md:2027 layer L21: ring L7, word L21 (store), label none; section [Databases] 1 -->
```zed
orders: OrderId ->? { total: rat, note: Utf8String | #none }
  with store(postgres(dbUrl, table: "orders", schema: sql("db/orders.sql")));

n = orders[id]?.note;     // Utf8String | #none | #notFound | #dbError
```

<!-- README.md:2064 layer L18: ring L2, word L18 (@memoized), label none; section [Incremental updates] 1 -->
```zed
// sales is keyed by SaleId; each sale has a region and an amount.
@memoized
report = sales
  .group(s -> s.region)
  .map(rows -> rows.map(s -> s.amount).sum);
```

<!-- README.md:2117 layer L15: ring L10, word L15 (@ensure), label none; section [Ranges and refinements] 1 -->
```zed
struct Span { lo: int, hi: int[lo..] }

width(positional s: Span) = s.hi - s.lo;   // inferred: int[0..]
// bad = Span(lo: 3, hi: 1);               // ✗ Argument outside its parameter's refinement: hi must be at least lo

@ensure odd(positional x) = (x * 2 + 1).refine(v -> v < 100);
                                           // inferred: x <= 49
a = odd(12);
// b = odd(60);                            // ✗ Undischargeable `@ensure`: 60 > 49
```

<!-- README.md:2147 layer L13: ring L7, word L13 (taint), label none; section [Units and taint] 1 -->
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

<!-- README.md:2177 layer L18: ring L5, word L18 (@noalloc), label none; section [Cost] 1 -->
```zed
@cost(xs::len)
@fused
sumSquares(positional xs: [f64]) = xs.map(x -> x * x) >< (+);

@cost(xs::len * log(xs::len))
ranked(positional xs: [int]) = xs.sort(desc x -> x);

@noalloc
lerp(positional a: f64, positional b: f64, positional t: f64) = a * (1 - t) + b * t;
```

<!-- README.md:2212 layer L20: ring L10, word L20 (Json), label none; section [Partial evaluation] 1 -->
```zed
struct User { id: int, name: Utf8String }

ok: User | #parseError(pos: int, msg: Utf8String) = Json.decode("{\"id\": 5, \"name\": \"John\"}");
// the constant User(id: 5, name: "John")

bad: User | #parseError(pos: int, msg: Utf8String) = Json.decode("{\"id\": \"five\"}");
// the constant #parseError(pos: 7, msg: "expected int for field 'id', got string")
```

<!-- README.md:2237 layer L11: ring L3, word L11 (::values), label none; section [Reflection] 1 -->
```zed
type Size = #small | #medium | #large;

sizes = Size::values;       // {#large, #medium, #small}: atoms sort by name
names = User::fields;       // the fields of the User struct above, by name and type
```

<!-- README.md:2260 layer L20: ring L20, word L20 (serialize), label none; section [Grammars] 1 -->
```zed
struct Vec3 grammar { "(" x: f64 "," y: f64 "," z: f64 ")" }

v = Vec3.parse("(1.0, 2.0, 3.0)") else Vec3(x: 0, y: 0, z: 0);
s = v.serialize;       // "(1.0,2.0,3.0)"
```

<!-- README.md:2276 layer L20: ring L20, word L3 (map), label none; section [Grammars] 2 -->
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

<!-- README.md:2301 layer L20: ring L20, word L7 (u8), label none; section [Grammars] 3 -->
```zed
struct Chunk grammar {
  n: int with bits(32) with endian(#big)
  kind: u8* with length(4)
  data: u8* with length(n)
  crc: int with bits(32) with endian(#big)
}
```

<!-- README.md:2324 layer L22: ring L3, word L22 (expand), label none; section [Symbolic math] 1 -->
```zed
p = ((x: rat) -> (x + 1r)^2)::source;
e = expand(p);          // x^2 + 2r * x + 1r
d = derivative(p);      // 2r * x + 2r
```

<!-- README.md:2348 layer L1: ring L1, word none, label none; section [Tests next to the code] 1 -->
```zed
double(positional x) = x * 2 test { 0 -> 0, 2 -> 4, -3 -> -6 }
```

<!-- README.md:2367 layer L15: ring L15, word L5 (sort), label none; section [Laws] 1 -->
```zed
// double is the function from Tests next to the code above.
law doubleIsSum(x: int) = double(x) == x + x;
law addComm(a: int, b: int) = a + b == b + a;
law sortTwice(xs: [int]) = xs.sort(asc x -> x).sort(asc x -> x) == xs.sort(asc x -> x);
```

<!-- README.md:2398 layer L15: ring L15, word L4 (flatMap), label none; section [Model checking] 1 -->
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
    with initial R = { Junction(ns: #red, ew: #red) };
};

law neverBothGreen(ns: Signal, ew: Signal) =
  (Junction(ns: ns, ew: ew) in reachable.R).implies(ns == #red || ew == #red);
```

<!-- README.md:2450 layer L7: ring L7, word L7 (@stateless), label none; section [Calling C, and being called from C] 1 -->
```zed
@foreign("m", "cbrt") @stateless cbrt: (positional x: f64) -> f64;

root = cbrt(8) else f64(0);

@export("c", "zed_score")
score(positional a: f64, positional b: f64) = (7 * a + 3 * b) / 10;
```
