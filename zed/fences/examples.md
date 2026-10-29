<!-- The `zed` fences of the spec's EXAMPLES.md, copied by sync.py: do not edit. -->

<!-- EXAMPLES.md:24 layer L3: ring L3, word none, label none -->
```zed
// [d4*] sec:ports, sec:tour_grammar — hello, world
main() -> (stdout: Lines) {
  stdout <- ["Hello, world!"];
}
```

<!-- EXAMPLES.md:33 layer L3: ring L1, word L3 (map), label none -->
```zed
// [d4] sec:tour_grammar — echo, upper-cased
main(stdin: Lines) -> (stdout: Lines) {
  stdout <- stdin.map(l -> l.upper);
}
```

<!-- EXAMPLES.md:40 layer L8: ring L8, word L5 (rank), label none -->
```zed
// [d4] sec:grouping, sec:remap_law (Ranking) — word frequencies, most common first
main(fs: Files) -> (stdout: Lines) {          // fs : Path ->? String | #ioError, the file port (sec:ports)
  text   = fs["input.txt"] else "";            // else strips #ioError and #notFound alike
  counts = text.split(" ").group(w -> w.lower).count;          // Lower ->? int
  lines  = counts as (w -> n) into (desc n -> w -> "${w}: ${n}"); // rank -> (w -> String); ties share a rank
  stdout <- lines.rank;                                        // the rank pass: one dense rank per line
}
```

<!-- EXAMPLES.md:52 layer L8: ring L8, word L4 (flatMap), label none -->
```zed
// [d4] sec:order, sec:remap_law — the same over a stream, where words are keyed by line and position
main(stdin: Lines) -> (stdout: Lines) {
  words  = stdin.flatMap(l -> l.split(" "));                             // LineNo -> int[0..<_] -> String
  counts = words as (l -> i -> w) into (w.lower -> (l, i) -> 1) >< (+);  // Lower ->? int
  stdout <- ["${counts::card} distinct words"];
}
```

<!-- EXAMPLES.md:65 layer L10: ring L10, word none, label none -->
```zed
// [d4] sec:tour_basics, sec:lexical
x = 42;                          // int, inferred domain int[42..=42]: a singleton, a subtype of every interval containing it
port: int[1..=65535] = 8080;     // an ascription where the domain carries intent
name = "Zed";
ok = true;
color = #green;                  // an atom: a value that is its own type
pair = (1, "one");               // a tuple
a, b = pair;                     // destructuring; arity must match
_, second = pair;                // _ discards
first = pair[0];                 // a tuple is indexed like any morphism; a literal index selects the component's type: int
```

<!-- EXAMPLES.md:78 layer L1: ring L1, word none, label none -->
```zed
// [d4] sec:lexical (the `=` row), sec:corner_cases — single assignment
f(x) {
  y = x + 1;
  y = y * 2;                     // ✗ rebinding in the same scope
  z = { y = 0; y };              // ✓ a nested block may shadow; its value is the trailing expression
  y + z
}
```

<!-- EXAMPLES.md:92 layer L10: ring L10, word none, label none -->
```zed
// [d4] sec:domains, sec:lexical
x   = 3;
q   = 7 div 2;             // 3      integers divide with div and mod (Euclidean)
r   = -7 mod 2;            // 1      (-7) mod 2 — unary minus binds tighter than mod; the remainder is never negative
h   = f64(7) / 2.0;        // 3.5    a cast is the type applied to the value
t   = 1r / 3r;             // exact: rat
big = 2 ** 100;            // int has no width; ** binds tighter than * and than unary minus, and associates to the right
m   = 1_000_000;  hex = 0xFF;  bits = 0b1011;  sci = 1.5e-3;
half = 0.5;                // never .5 — a float literal starts with a digit
y   = x ** 2 + 2*x + 1;
b: byte = 255;             // byte = int[0..=255]; 256 here is a type error, not a wrap
w: i32 = shl(1, 30);       // no bitwise operators: bitAnd, bitOr, shl are ordinary functions
z   = 7 / 2;               // ✗ `/` is for f64 and rat only
```

<!-- EXAMPLES.md:108 layer L10: ring L10, word none, label none, documentation notation -->
```zed
// [d4] sec:failure, sec:domains — division is total on the domain that excludes zero
(div) : ((int, int \ 0) -> int) & ((int, 0) -> #divByZero)   // the built-in's type, shown as a judgment — no ';' (sec:lexical)
half(n) = n div 2;                       // int: the literal 2 selects the first arrow
ratio(positional a, positional b) = a div b;  // int | #divByZero: b's domain straddles both arrows
r1 = ratio(a, b) else 0;
r2 = match ratio(a, b) { #divByZero -> 0, v -> v };
```

<!-- EXAMPLES.md:121 layer L3: ring L1, word L3 (split), label none -->
```zed
// [d4] sec:lexical, sec:order
s  = "Hello" ++ ", " ++ "world";     // ++ concatenates: associative, not commutative
t  = "total: ${a + b}";              // ≡ "total: " ++ String(a + b)
n  = s.len;                          // scalar values, not bytes; the same number as s::len
u  = s.upper;  l = s.lower;
ws = s.split(" ");                   // [String]
c  = s[0];                           // Scalar; s[i] for i : int is Scalar | #notFound
doc = """
  line one
  line two
  """;
esc = "tab\t quote\" newline\n";
```

<!-- EXAMPLES.md:136 layer L3: ring L1, word none, label L3 -->
```zed
// [d4] sec:order, sec:domains — comparing a scalar with a one-element literal
// layer L3
isComment = line[0] == "#";          // the literal adopts Scalar, as 2 adopts int[0..<5] in a[2]
```

<!-- EXAMPLES.md:142 layer L8: ring L8, word L5 (rank), label none -->
```zed
// [d4*] [lib] sec:remap_law, sec:order — a string is a collection; upper on a Scalar is a library word
chars    = for ch in s { ch };                            // the string itself, key by key
shouted  = s.map(ch -> ch.upper);                          // int[0..<len] -> Scalar: a String again
reversed = s as (i -> ch) into (s::len - 1 - i -> ch);     // a bijective rekey
noSpaces = s.where(ch -> ch != " ").rank;                  // where leaves gaps; the rank pass closes them
```

<!-- EXAMPLES.md:150 layer L5: ring L1, word L5 (slice), label none -->
```zed
// [lib] words the library audit (sec:tooling) will settle; nothing above depends on them
sub  = s.slice(0, 5);        // "Hello": restrict the rank domain to 0..<5, then re-rank
has  = s.contains("world");
trim = "  x ".trim;
ls   = text.lines;           // split on line breaks
joined = ws.concat(" ");     // the inverse of split
```

<!-- EXAMPLES.md:163 layer L10: ring L10, word L1 (String), label none -->
```zed
// [d4] sec:tour_basics
sign(x) = if x < 0 { -1 } else if x == 0 { 0 } else { 1 };
grade(score) -> String {
  if score >= 90 { "A" }
  else if score >= 80 { "B" }
  else { "C" }
}
label = if ok { "yes" } else { "no" };
```

<!-- EXAMPLES.md:174 layer L1: ring L1, word none, label none -->
```zed
// [d4] sec:lexical (precedence) — && and || are selection nodes; comparisons bind tighter than &&, and && tighter than ||
adult   = age >= 18 && country == "NZ";       // comparisons bind tighter than &&
allowed = age >= 18 && member || override;      // (age >= 18 && member) || override
```

<!-- EXAMPLES.md:180 layer L6: ring L6, word none, label none -->
```zed
// [d4] sec:generations — a conditional write goes through the value
collatz = loop {
  n' = if (n mod 2) == 0 { n div 2 } else { 3 * n + 1 } with n = 27;
  until n' == 1;
};
```

<!-- EXAMPLES.md:192 layer L10: ring L10, word L1 (String), label none -->
```zed
// [d4] sec:tour_basics
double(positional x) = x * 2;                        // equation form; types inferred from the body
double: (int) -> int;                                // or a signature declaration on its own line — a statement, so it takes ';'
clamp(positional v, positional lo, positional hi) -> int { if v < lo { lo } else if v > hi { hi } else { v } }
greet(positional name: String, punct = "!") = "Hi, " ++ name ++ punct;
g1 = greet("Al");                                    // "Hi, Al!"  — the default fills in
g2 = greet("Al", punct: "?");                        // positional arguments first, then named
y  = 5.double.clamp(0, 8);                           // ≡ clamp(double(5), 0, 8); a call on a literal is fine
```

<!-- EXAMPLES.md:203 layer L1: ring L1, word none, label none -->
```zed
// [d4] sec:values_morphisms, sec:corner_cases — lambdas and closures
inc   = x -> x + 1;                    // brace-free; a brace after the arrow is a block, so a set-valued body is x -> ({ x })
add   = (a, b) -> a + b;
apply(f, x) = f(x);
compose(positional f, positional g) = x -> f(g(x));
twice(positional f) = compose(f, f);
five  = twice(inc)(3);
adder(positional n) = x -> x + n;        // closures capture values, never variables
add5  = adder(5);
seven = add5(2);
```

<!-- EXAMPLES.md:216 layer L1: ring L1, word L1 (String), label none -->
```zed
// [d4] sec:values_morphisms — named arguments, and one level of application
g3   = greet("Al", ...);                // currying leaves out named parameters: called g3(punct: "?") or g3()
add1 = add[1];                          // brackets index one level: the section b -> add(1, b)
add1b = b -> add(1, b);                 // the lambda spelling, always available
g4   = greet();                         // ✗ arity: name has no default. The menu names greet[…] and the lambda
g5   = greet(name: "Al");               // ✗ name is positional, so it is passed by position
onKey(positional k, handler: (key: String) -> String) = handler(key: k);
shout = onKey("a", handler: key -> key ++ "!");  // the type names key, so the lambda's key is named
bad  = onKey("a", handler: s -> s);     // ✗ the type names the parameter key. The menu renames s to key
```

<!-- EXAMPLES.md:230 layer L3: ring L3, word L3 (map), label none -->
```zed
// [d4] sec:values_morphisms, sec:power — several results
divmod(positional a, positional b) { return a div b, a mod b; }  // one return; a comma-list exports a tuple
q, r = divmod(7, 2);

stats(positional data: [f64]) {
  n = f64(data::len);
  mean = data.sum / n;
  sd   = (data.map(x -> (x - mean) ** 2).sum / n).sqrt;
  return { mean:, sd: };                 // a record display: one export, two fields, each pruned on its own
}
m = stats(xs).mean;
```

<!-- EXAMPLES.md:244 layer L2: ring L1, word none, label L2 -->
```zed
// [d4] sec:type_language, sec:lexical — overloading is a second arrow of one name
// layer L2
show(positional x: int)   = "int ${x}";
show(positional p: Point) = "(${p.x}, ${p.y})";     // show : (int -> String) & (Point -> String)
```

<!-- EXAMPLES.md:257 layer L6: ring L6, word L5 (zip), label none -->
```zed
// [d4] sec:tour_collections, sec:type_language (bound table)
xs  = [3, 1, 4, 1, 5];                   // [int] ≡ int[0..<5] -> int
n   = xs::len;                            // 5
h   = xs[0];                              // int — 0 is provably in the domain
at(i) = xs[i];                            // int | #notFound for i : int; int for i : int[0..<5]
ys  = xs.map(x -> x * 10);
big = xs.where(x -> x > 2);               // keys 0, 2, 4 survive: a subdomain, not a renumbering
tot = xs.sum;   mx = xs.max;   cnt = xs.count;
fb  = xs.where(x -> x > 3).first;         // int | #none
sq  = for i in 0..<10 { i * i };
ev  = for i in 0..<10 where (i mod 2) == 0 { i };      // keys 0, 2, 4, … survive
cumul[i] = cumul[i-1] + xs[i] with cumul[-1] = 0;          // running sum: a scan, domain inferred from xs
last = cumul.last else 0;
pairs = xs.zip(ys);                        // (int, int) per key; same domain, so no assertion is owed
```

<!-- EXAMPLES.md:274 layer L5: ring L1, word none, label L5 -->
```zed
// [d4*] sec:order, sec:joins — concatenation on rank keys is the offset kind
// layer L5
all = xs ++ ys;                           // length 10; xs ++ xs is length 10 too (no collision on rank keys)
```

<!-- EXAMPLES.md:280 layer L5: ring L5, word L5 (sort), label none -->
```zed
// [d4] sec:remap_law (Ranking) — sorting
srt  = xs.sort(desc x -> x);              // [5, 4, 3, 1, 1]: a ranked source sorts to a flat ranked result
top2 = srt.slice(0, 2);                   // [lib]
byLen = words.sort(asc w -> w.len);       // words : [String] — flat again
```

<!-- EXAMPLES.md:289 layer L8: ring L8, word none, label none -->
```zed
// [d4*] sec:remap_law — reversing is a bijective rekey; [lib] the word for it
rev  = xs as (i -> x) into (xs::len - 1 - i -> x);
rev2 = xs.reverse;
```

<!-- EXAMPLES.md:295 layer L5: ring L3, word L5 (takeWhile), label none -->
```zed
// [lib] sec:tooling — sequence vocabulary the library audit will fix
has   = xs.contains(3);
some  = xs.any(x -> x > 4);
every = xs.all(x -> x > 0);
tk    = xs.take(2);   dr = xs.drop(2);   tw = xs.takeWhile(x -> x < 4);
idx   = xs.indexOf(4);                  // int | #none
flat  = [[1, 2], [3]].rank;             // [1, 2, 3]: the rank pass over the lexicographic order
```

<!-- EXAMPLES.md:309 layer L8: ring L8, word L5 (patch), label none -->
```zed
// [d4] sec:values_morphisms, sec:type_language (m[k] row), sec:generations
ages  = { "ann" -> 31, "bob" -> 27 };     // {"ann", "bob"} -> int
a     = ages["ann"];                       // int: the key is provably present
b     = ages[who];                         // int | #notFound when who : String
c     = ages[who] else 0;
in1   = who in ages::domain;               // membership is a test on the domain
names = ages::domain;                      // the key set
size  = ages::card;
older = ages.map(n -> n + 1);              // same keys
adult = ages.where(n -> n >= 18);          // a subdomain
total = ages.sum;
inv   = ages as (name -> age) into (age -> name -> _);   // age ->? (set of names): an inversion groups
ages2 = ages.patch({ "cy" -> [#insert(40)] });        // a delta: per key, a rank of edits
ages3 = ages.patch({ "bob" -> [#update(n -> n + 1)], "ann" -> [#delete] });
```

<!-- EXAMPLES.md:326 layer L5: ring L3, word L5 (patch), label none -->
```zed
// [d4] sec:generations — one edit per key needs no rank brackets: patch's second arrow
ages4 = ages.patch({ "cy" -> #insert(40) });
```

<!-- EXAMPLES.md:331 layer L5: ring L1, word L5 (maxBy), label none -->
```zed
// [d4] sec:grouping, sec:tour_collections — keys that are not unique group; keys that are, rekey
byId    = users.rekey(u -> u.id);          // ✗ unless u.id is witnessed injective
byId2   = users.group(u -> u.id);          // Id ->? (UserKey -> User)
byLower = words.group(w -> w.lower);       // Lower ->? (i -> w)
counts  = byLower.count;                   // Lower ->? int
best    = scores.maxBy(v -> v);            // (score ->? (name -> score)) | #none: the whole maximal class; #none only if scores is empty
one     = best.first;
```

<!-- EXAMPLES.md:343 layer L7: ring L7, word L7 (order), label none -->
```zed
// [d4] sec:order — every level has an order, and a sort is placed only where a fold reads it
struct Entry { score: int with order(#desc), name: String with order(collate: "de"), id: int }
board = entrySet.rank;                        // entrySet : a set of Entry; [Entry] by score high to low, then name in German collation, then id
total = ages >< (+);                          // + is commutative: read in storage order, no sort
line  = ages.map(a -> "${a} ") >< (++);       // ++ is not: the ages in the code point order of the names, one sort
least = ages.first;                           // int | #none: the same order of the same map, so the same sorted view; a top-1 selection
fsum2 = weights >< (+);                       // weights : String -> f64; a float + is an exact sum, so no sort
fprod = weights >< (*);                       // a float * takes the canonical tree, which follows the key order, so it sorts, and unordered would not
byLen2 = words.sort(by: (a, b) -> a.len <= b.len);  // a comparator: a total preorder; ties completed by the natural order
```

<!-- EXAMPLES.md:355 layer L5: ring L3, word L5 (diff), label none -->
```zed
// [d4] sec:tour_collections — sets are self-maps
tags   = { #red, #green };
has    = #red in tags;                    // the same test as `#red in tags::domain`
only   = tags.diff(other);
both   = tags.union(other);               // union is also the spelling of ⊔ that a fixpoint loop needs
common = tags.intersect(other);           // [lib] intersect — the meet is a library word
```

<!-- EXAMPLES.md:366 layer L9: ring L9, word L3 (foldl), label none -->
```zed
// [d4] sec:reduction
total = readings >< (+);                        // one level removed
avg   = (data >< (+)) / f64(data::len);         // >< binds looser than arithmetic: parenthesize
mx    = temps >< max else 0;                    // an explicit default for a possibly empty level
cnt   = words.count;
digits = [1, 2, 3];
num   = digits.foldl(0, (acc, d) -> acc * 10 + d);   // 123; non-associative, so the rank is required
fsum  = samples >< (+) unordered;               // floats: give up bit-reproducibility for speed, visibly
```

<!-- EXAMPLES.md:377 layer L8: ring L8, word L5 (sort), label none -->
```zed
// [d4] sec:grouping, sec:remap_law — group, then reduce per group
struct Sale { region: String, product: String, amount: rat }
byRegion = sales.group(s -> s.region);                              // Region ->? (i -> Sale)
totals   = byRegion.map(rows -> rows.map(r -> r.amount).sum);       // Region ->? rat
pivot    = sales as (i -> s) into (s.region -> s.product -> i >< (+) -> s.amount);   // Region ->? Product ->? rat
ranked   = totals.sort(desc t -> t);                                // rank -> (Region -> rat)
```

<!-- EXAMPLES.md:388 layer L14: ring L8, word L14 (matmul), label none -->
```zed
// [d4] sec:tour_joins — joins in both registers
paid   = orders.join(payments, on: #orderId, kind: #left);
paid2  = for o in orders { payment = payments[o.orderId] else #none; (o, payment) };
inner  = for o in orders where o.orderId in payments::domain { (o, payments[o.orderId]) };
shipped = for o in orders, s in shipments where o.orderId == s.orderId { (o, s) };   // product form, planned as a join: ((OrderId, ShipmentId)) ->? (Order, Shipment); shipments : ShipmentId -> Shipment
pairs  = for i in 0..<n, j in i+1..<n { (i, j) };   // a domain may mention another generator's binder: j nests inside i, keyed (i, j) — the same family as `for i in 0..<n, j in 0..<n where i < j`
unpaid = orders.diff(payments, on: #orderId);
unpaid2 = orders.where(o -> payments[o.orderId] is #notFound);
prod   = a.matmul(b);
prod2  = (a, b) into (r -> k -> c >< (+) -> a[r][c] * b[c][k]);
```

<!-- EXAMPLES.md:401 layer L5: ring L1, word L5 (join), label none -->
```zed
// [d4*] sec:joins — join residues carry the shape: a side whose join key is unique erases its residue level
full     = orders.join(payments, on: #orderId, kind: #outer);   // OrderId ->? (Order | #none, Payment | #none): both sides unique, so flat
// with several payments per order (payments : PaymentId -> Payment, orderId a field), the payment residue level appears:
perOrder = orders.join(payments, on: #orderId);                 // OrderId ->? PaymentId -> (Order, Payment): inner, the default kind
missingPayment = orders.diff(payments, on: #orderId);                      // the left-only region, asked for directly
```

<!-- EXAMPLES.md:413 layer L2: ring L2, word none, label none -->
```zed
// [d4] sec:tour_basics
struct Point { x: f64, y: f64 }
p  = Point(x: 1.0, y: 2.0);
p2 = p with { x = 3.0 };                // an update is a new value
px = p.x;                               // p.x ≡ p[#x]
dist(positional a: Point, positional b: Point) = ((a.x - b.x) ** 2 + (a.y - b.y) ** 2).sqrt;
struct Circle { c: Point, r: f64 }
struct Round  { import Rect, r: f64 }   // field embedding: Rect's fields, plus r
```

<!-- EXAMPLES.md:424 layer L10: ring L10, word none, label none -->
```zed
// [d4] sec:domains — a field's refinement may name another field
struct Span { lo: int, hi: int[lo..] }
s  = Span(lo: 2, hi: 5);                 // the constructor checks hi >= lo
w  = s.hi - s.lo;                        // s.hi : int[s.lo..], so w : int[0..]
s2 = s with { hi = s.hi + 1 };           // still a Span: hi + 1 >= lo
```

<!-- EXAMPLES.md:432 layer L2: ring L1, word none, label L2 -->
```zed
// [d4*] sec:power (Vec3) — a constructor takes its fields by name only; `x:` supplies the variable x
// layer L2
x = 3.0;
y = 4.0;
q = Point(x:, y:);                 // Point(x: x, y: y)
// q = Point(3.0, 4.0);            // ✗ a constructor is called by name: Point(x: 3.0, y: 4.0)
```

<!-- EXAMPLES.md:441 layer L6: ring L6, word none, label none -->
```zed
// [d4] sec:tour_methods — methods: bare fields in scope; a prime on a field makes the receiver a result
Point.norm     = (x*x + y*y).sqrt;                  // pure: no primes
Point.scale(k) = Point(x: x * k, y: y * k);          // pure: returns a new Point
Point.move(positional dx, positional dy) { x' = x + dx; y' = y + dy; }  // (Point, f64, f64) -> Point
p3 = p.move(1.0, 0.0);                               // the moved point; p is unchanged
walk = loop {
  mutable pt = Point(x: 0.0, y: 0.0);
  pt*.move(1.0, 1.0);                                // pt' = pt.move(1.0, 1.0)
  until pt.x > 5.0;
};
```

<!-- EXAMPLES.md:454 layer L3: ring L3, word none, label none -->
```zed
// [d4*] sec:values_morphisms — an anonymous struct is a display keyed by field atoms
origin = { #x -> 0.0, #y -> 0.0 };      // has the fields of Point, so it is a Point
```

<!-- EXAMPLES.md:459 layer L2: ring L2, word none, label none -->
```zed
// [d4] sec:lexical, sec:type_language — the record display and a nested update path
origin2 = { x: 0.0, y: 0.0 };           // name: v is #name -> v — the same display as origin, spelled with field names
k  = Circle(c: p, r: 1.0);              // p : Point, from the first block of this section
k2 = k with { c.x = 0.0 };              // one level in: k with { c = k.c with { x = 0.0 } }
```

<!-- EXAMPLES.md:468 layer L2: ring L2, word none, label none -->
```zed
// [d4] sec:tour_basics, sec:failure
type Color = #red | #green | #blue;
next(positional c: Color) = match c { #red -> #green, #green -> #blue, #blue -> #red };

type Shape = Circle | Rect;
area(s: Shape) = match s {
  Circle(r:)      -> pi * r * r,       // fields by name; an omitted field is not matched
  Rect(lo:, hi:)  -> (hi.x - lo.x) * (hi.y - lo.y),
};                                       // exhaustive, or it does not compile
```

<!-- EXAMPLES.md:480 layer L10: ring L10, word none, label none -->
```zed
// [d4*] sec:type_language (recursive types), sec:failure — a recursive union with payload atoms
type Expr = #num(f64) | #add(Expr, Expr) | #mul(Expr, Expr);
eval(positional e: Expr) -> f64 {
  match e {
    #num(v)    -> v,
    #add(a, b) -> eval(a) + eval(b),
    #mul(a, b) -> eval(a) * eval(b),
  }
}
three = eval(#add(#num(1.0), #num(2.0)));
```

<!-- EXAMPLES.md:493 layer L2: ring L2, word L1 (String), label none -->
```zed
// [d4] sec:failure — a payload is a struct, so it is built and matched like one
type Fail = #syntaxError(pos: int, msg: String);
e1 = #syntaxError(pos: 3, msg: "unexpected )");  // built by name, like a struct
// e2 = #syntaxError(3, "unexpected )");         // ✗ a payload with named fields is built by name
position(f: Fail) = match f { #syntaxError(pos:) -> pos };   // matched by name too; msg omitted
```

<!-- EXAMPLES.md:501 layer L2: ring L2, word none, label none -->
```zed
// [d4] sec:type_language — same-shape structs are one type; tell them apart with a tag
struct Celsius    { deg: f64 }
struct Fahrenheit { deg: f64 }
type Temp = Celsius | Fahrenheit;        // = { deg: f64 }: the union collapses
show(positional t: Temp) = match t {
  Celsius(deg: d)    -> "${d} C",
  Fahrenheit(deg: d) -> "${d} F",             // ✗ unreachable: every Temp already matched the first arm
};
type Temp2 = #c(f64) | #f(f64);          // ✓ the atom is the identity
```

<!-- EXAMPLES.md:513 layer L3: ring L3, word none, label none -->
```zed
// [d4] sec:lexical — guards and range patterns in match arms
classify(n) = match n { 0 -> #zero, x where x < 0 -> #neg, _ -> #pos };
digit(n: int) = match n { 0..=9 -> #ok, _ -> #bad };
```

<!-- EXAMPLES.md:523 layer L3: ring L3, word L3 (where), label none, documentation notation -->
```zed
// [d4] sec:tour_failure
parse : (String) -> Config | #syntaxError(pos: int)     // an assumed input, shown as a type — no ';' (sec:lexical)
conf = parse(text) else defaultConfig;
port = parse(text)?.server?.port else 8080;
msg  = match parse(text) { #syntaxError(pos:) -> "bad at ${pos}", c -> c.name };
results = files.map(f -> read(f)).map(b -> parse(b));   // File -> Config | #syntaxError(pos: int) | #ioError | #notFound: the atoms ride through
good = results.where(r -> r is Config);
bad  = results.where(r -> r is not Config);
amounts = files.map(f -> int(read(f)));                 // int | #invalid | #ioError | #notFound
sumKept   = amounts.where(a -> a is int) >< (+);
sumZeroed = amounts.map(a -> a else 0) >< (+);
```

<!-- EXAMPLES.md:537 layer L10: ring L10, word none, label none -->
```zed
// [d4] sec:failure — declared propagation: the enclosing result type carries the atom
loadPort(path) -> int | #ioError | #notFound | #syntaxError(pos: int) {
  text = read(path);                     // String | #ioError | #notFound
  cfg  = parse(text);                    // Config | #syntaxError(pos) | #ioError | #notFound — the atoms select no arrow and flow on
  cfg.port
}
```

<!-- EXAMPLES.md:546 layer L10: ring L1, word L10 (refine), label none -->
```zed
// [d4] sec:domains — a refinement is a proof or a failure, never a crash
age  = int(input)?.refine(a -> a >= 0);          // int | #invalid
safe = age else 0;
```

<!-- EXAMPLES.md:552 layer L10: ring L10, word none, label none -->
```zed
// [d4*] sec:failure — your own failures are atoms; the caller decides
withdraw(positional a: Account, positional amt: rat) -> Account | #insufficient(short: rat) {
  if amt > a.bal { #insufficient(short: amt - a.bal) } else { a with { bal = a.bal - amt } }
}
a2 = withdraw(a, 10r) else a;                                        // keep the old account on failure
a3 = withdraw(a, 10r) else #insufficient(short: _) -> a with { frozen = true };   // pattern form
```

<!-- EXAMPLES.md:565 layer L6: ring L6, word L6 (::frames), label none -->
```zed
// [d4] sec:tour_loops — a simulation
sim = loop {
  pos' = pos + vel * dt   with pos = p0;
  vel' = vel + acc * dt   with vel = v0;
  until pos.y < 0.0;
};
final   = sim.pos;                        // the last generation's value
history = sim::frames;                    // int[0..<sim::len] -> Frame, kept only because it is demanded
```

<!-- EXAMPLES.md:576 layer L6: ring L6, word none, label none -->
```zed
// [d4] sec:tour_methods — a mutable receiver inside a loop
run = loop {
  mutable c = Counter(n: 0, hi: 9);
  prev = c*.bump(3);                      // c', prev = c.bump(3)
  until prev > 20;
};
```

<!-- EXAMPLES.md:585 layer L6: ring L6, word none, label none -->
```zed
// [d4] sec:generations — the three guards
once    = loop { i' = i + 1 with i = 0; until i' == 10; };     // tested at the end of a step: runs at least once
maybe   = loop { i' = i + 1 with i = 0; while i < 10; };       // tested at the start: may run zero times
counted = loop t { x' = step(x) with x = seed; until t == 99; };   // t is the step ordinal
```

<!-- EXAMPLES.md:592 layer L6: ring L6, word none, label none -->
```zed
// [d4*] sec:generations — break carries a value out of the frame
found = loop {
  i' = i + 1 with i = 0;
  hit = if xs[i] == target { break i } else { i };
  while i < xs::len;
};
```

<!-- EXAMPLES.md:601 layer L6: ring L6, word none, label none -->
```zed
// [d4] sec:tour_loops, sec:kernel — a convergence-shaped guard: without evidence for every T-Fix premise of simplifyOnce (monotone and inflationary on a carrier with ACC, and total) this is a gen that runs serially; with it, a fix (T-Fix)
simplified = loop {
  terms' = simplifyOnce(terms) with terms = input;
  until terms' == terms;                  // convergence-shaped: consumed as the termination test
};
```

<!-- EXAMPLES.md:609 layer L6: ring L6, word L6 (::frames), label none -->
```zed
// [d4] sec:generations, sec:power — history, retention, and a piecewise family
run  = loop t { while t < edits::len && !closed; doc' = doc.patch(edits[t]) with doc = empty; };
past = run::frames[run::len - 2].doc else empty;

x[i in 0..<warm]  = warmup(i);
x[i in warm..<n]  = x[i-1] + delta(i);    // one family, two pieces; overlapping domains would collide
```

<!-- EXAMPLES.md:618 layer L6: ring L6, word none, label none -->
```zed
// [d4] sec:generations — local hides a generation variable from the loop's result (a step-local is never in the frame)
s = loop {
  local tally' = tally + step(a) with tally = 0;   // a generation variable, kept out of s
  a' = a + 1 with a = 0;
  until a' > 100;
};
```

<!-- EXAMPLES.md:631 layer L6: ring L6, word none, label none -->
```zed
// [d4*] sec:tour_basics, sec:tour_loops
fact(positional n) = if n == 0 { 1 } else { n * fact(n - 1) };
fib(positional n)  = if n < 2 { n } else { fib(n - 1) + fib(n - 2) };
fibs[n in 2..] = fibs[n-1] + fibs[n-2] with fibs[0] = 0, fibs[1] = 1;   // the same recurrence as a family
f10 = fibs[10];                                                          // computed on demand, memoized as a value
gcd(positional a, positional b) = if b == 0 { a } else { gcd(b, a mod b) };
even(positional n) = if n == 0 { true } else { odd(n - 1) };              // mutual recursion is one fix region
odd(positional n)  = if n == 0 { false } else { even(n - 1) };
```

<!-- EXAMPLES.md:642 layer L6: ring L6, word L3 (map), label none -->
```zed
// [d4*] sec:power — a pseudo-random sequence is a recurrence with a seed
next(positional s) = (s * 6364136223846793005 + 1442695040888963407) mod (2 ** 64);
rnd[i in 0..] = next(rnd[i-1]) with rnd[-1] = seed;
dice = rnd.map(r -> ((r div 2 ** 32) mod 6) + 1);   // the high bits: an LCG's low bit alternates
tenRolls = for i in 0..<10 { dice[i] };
```

<!-- EXAMPLES.md:652 layer L10: ring L10, word L3 (foldl), label none -->
```zed
// [d4*] sec:type_language (recursive types), sec:tour_basics
type Tree = #leaf | Node;
struct Node { l: Tree, v: int, r: Tree }

size(positional t: Tree) = match t { #leaf -> 0, Node(l:, r:) -> 1 + size(l) + size(r) };
depth(positional t: Tree) = t.fold(n -> match n { #leaf -> 0, Node(l:, r:) -> 1 + max(l, r) });   // .fold hands the algebra one layer, each subtree already replaced by its depth; size above is recognized as the fold of 1 + l + r

insert(positional t: Tree, positional x: int) -> Tree {
  match t {
    #leaf -> Node(l: #leaf, v: x, r: #leaf),
    Node(l:, v:, r:) -> if x < v { Node(l: insert(l, x), v:, r:) }
                        else     { Node(l:, v:, r: insert(r, x)) },
  }
}
tree = xs.foldl(#leaf, insert);

inorder(positional t: Tree) -> [int] {
  match t { #leaf -> [], Node(l:, v:, r:) -> inorder(l) ++ [v] ++ inorder(r) }
}
```

<!-- EXAMPLES.md:676 layer L10: ring L10, word L4 (flatMap), label none -->
```zed
// [d4*] sec:values_morphisms, sec:generations — reachability is a fixpoint on sets
edges: Id ->? [Id] = { 1 -> [2, 3], 2 -> [4], 3 -> [4], 4 -> [] };
succ(positional s) = s.flatMap(n -> edges[n] else []).image;  // [lib] image: the set of values
reach = loop {
  r' = r.union(succ(r)) with r = { start };             // r' = r ⊔ e: monotone, so the guard below is read as the fixpoint's test
  until r' == r;
};
```

<!-- EXAMPLES.md:686 layer L16: ring L10, word L16 (@idempotent), label none -->
```zed
// [d4*] sec:generations, sec:corner_cases, sec:kernel — shortest paths: a fixpoint that lowers distances, on a carrier with a bottom.
//   Dist has the explicit bottom #inf, so every step is total on the carrier (T-Fix): an unreached
//   node holds #inf rather than being absent. The step is the join-update form x' = x ⊔ e with
//   ⊔ = minD (the fix row of sec:kernel), so its evidence is syntactic: minD's declared
//   associative/commutative/idempotent, addD monotone in d; weights are nonnegative, so a distance only falls and never below 0
type Dist = int[0..] | #inf;
addD(positional d: Dist, positional w: int[0..]) -> Dist { if d is #inf { #inf } else { d + w } }
@associative @commutative @idempotent
minD(positional a: Dist, positional b: Dist) -> Dist { if a is #inf { b } else if b is #inf { a } else { min(a, b) } }
dist = loop {
  d'[v in nodes] = minD(d[v], (for u in preds[v] { addD(d[u], w[u][v]) }) >< minD else #inf)
                   with d = for v in nodes { if v == start { 0 } else { #inf } };
  until d' == d;
};
```

<!-- EXAMPLES.md:709 layer L5: ring L3, word L5 (last), label none -->
```zed
// [d4] sec:type_resolution
head(positional xs) = xs[0];                        // (int[0..<n] -> T) -> T | #notFound
swap(p) { a, b = p; (b, a) }
type Stack(T) = [T];
push(s: Stack(T), x: T) = s ++ [x];
top(s: Stack(T)) = s.last;               // T | #none
```

<!-- EXAMPLES.md:718 layer L10: ring L10, word L1 (String), label none -->
```zed
// [d4] sec:type_language, sec:type_notation — an interface is a named structural type
interface Named { name: String }
greet(positional n: Named) = "Hi, ${n.name}";
struct User { name: String, id: int }
struct Cat  { name: String }
g1 = greet(User(name: "Al", id: 1));
g2 = greet(Cat(name: "Tom"));
```

<!-- EXAMPLES.md:728 layer L10: ring L10, word none, label none -->
```zed
// [d4] sec:values_morphisms — a required name may be a field or a function in scope
interface HasArea { area: f64 }
describe(positional s: HasArea) = "area ${s.area}";
d = describe(Circle(c: origin, r: 1.0));  // area(s: Shape) is in scope, and s.area ≡ area(s:)
```

<!-- EXAMPLES.md:735 layer L2: ring L2, word none, label none -->
```zed
// [d4] sec:type_language — a parameterized structural type
type Pair(A, B) = { fst: A, snd: B };
```

<!-- EXAMPLES.md:744 layer L2: ring L2, word none, label none -->
```zed
// [d4] sec:units — geometry/shapes.zed
struct Point { x: f64, y: f64 }
local sq(positional v) = v * v;            // not exported
dist(positional a: Point, positional b: Point) = (sq(a.x - b.x) + sq(a.y - b.y)).sqrt;
```

<!-- EXAMPLES.md:751 layer L2: ring L2, word none, label none -->
```zed
// [d4] sec:units — main.zed: one import form per unit, not all at once
import geometry.shapes.{Point, dist};    // unqualified; the alternatives are `import geometry.shapes;` (shapes.dist)
                                         //   and `import geometry.shapes as g;` (g.dist)
                                         //   a pinned form adds @hash("…"): the build writes the pin, and the file is then checked, not re-resolved
far = dist(Point(x: 0.0, y: 0.0), Point(x: 3.0, y: 4.0));
```

<!-- EXAMPLES.md:763 layer L3: ring L1, word L3 (map), label none -->
```zed
// [d4] sec:tour_failure, sec:ports — fs : Files, a port parameter of main (Files = Path ->? String | #ioError)
text  = fs["notes.txt"] else "";                // String: else strips #ioError and #notFound
texts = files.map(f -> fs[f]);                  // Path -> String | #ioError | #notFound
```

<!-- EXAMPLES.md:769 layer L21: ring L7, word L21 (store), label none -->
```zed
// [d4] sec:tour_grammar, sec:ports — a stored collection is always partial, and writes are deltas
orders: OrderId ->? { total: rat, note: String | #none }
  with store(postgres(dbUrl, table: "orders", schema: sql("db/orders.sql")));
n   = orders[id]?.note;
run = loop t {
  orders' = orders.patch(toEdits(reqs[t]));     // committed as one transaction at the step boundary
  while t in reqs::domain;
};
```

<!-- EXAMPLES.md:780 layer L21: ring L7, word L21 (store), label none -->
```zed
// [d4*] sec:ports — a key-value store and a file-backed table
cache: String ->? [byte] with store(kv(endpoint));
config: String ->? String with store(file("app.cfg", KeyVal));   // the format is a struct grammar
```

<!-- EXAMPLES.md:786 layer L21: ring L7, word L21 (store), label none -->
```zed
// [d4] sec:ports, sec:staging — a timeout is declared on the port and adds #timeout to its failure member
cache: String ->? [byte] with store(kv(endpoint)) with timeout(200 with units("ms"));   // lookup: [byte] | #ioError | #timeout | #notFound
hit = cache[key] else fetch(key);                                                   // else strips #timeout with the rest: a read that ran out of time is a miss
```

<!-- EXAMPLES.md:792 layer L7: ring L3, word L7 (Stream), label none -->
```zed
// [prop] — ports the spec does not yet name
main(args: [String], env: String ->? String, clock: Stream(Instant)) -> (stdout: Lines, exit: int) { … }
page = http.get(url);                            // Response | #httpError(status: int) | #ioError
```

<!-- EXAMPLES.md:802 layer L5: ring L1, word L5 (chunkBy), label none -->
```zed
// [d4] sec:tour_loops, sec:power
sessions = events.chunkBy(e -> e.userId);
report   = sessions.map(s -> summarize(s));
bigOnes  = events.where(e -> e.size > 1_000_000);
```

<!-- EXAMPLES.md:809 layer L5: ring L1, word L4 (tag), label L5 -->
```zed
// [d4] sec:order — two sources into one: tag the origin, or the keys collide
// layer L5
merged = a.tag(#a) ++ b.tag(#b);          // (#a | #b) -> origin -> V
```

<!-- EXAMPLES.md:815 layer L10: ring L10, word L4 (flatMap), label none -->
```zed
// [d4*] sec:lexical (the emit row) — one input, several outputs, when the signature says so
expand(positional n: int) -> [int] { emit n; emit n * 10; }
out = xs.flatMap(expand);                 // int[0..<5] -> int[0..<2] -> int
```

<!-- EXAMPLES.md:821 layer L7: ring L2, word L7 (Stream), label none -->
```zed
// [d4] sec:power — a request/response service is a map over the request stream
main(req: Stream(Query)) -> (resp: Stream(Answer)) {
  resp <- req.map(q -> lookup(db, q) else #unknown);
}
```

<!-- EXAMPLES.md:828 layer L12: ring L7, word L12 (units), label none -->
```zed
// [prop] — windows and merge by arrival
perMinute = events.window(60 with units("s")).map(w -> w.count);
```

<!-- EXAMPLES.md:835 layer L18: ring L10, word L18 (@memoized), label none -->
```zed
// [d4] sec:tooling, sec:power, sec:property_tracking
double(positional x) = x * 2 test { 0 -> 0, 2 -> 4, -3 -> -6 }
clamp(positional v, positional lo, positional hi) -> int { if v < lo { lo } else if v > hi { hi } else { v } }
  test { (5, 0, 8) -> 5, (-1, 0, 8) -> 0, (9, 0, 8) -> 8 }
@exhaustive romanDigit(n: int[1..=9]) -> String { … }       // all nine inputs run at build time
@associative @commutative combine(positional a, positional b) = …;                 // a claim the checker tests, and downgrades on a counterexample
@memoized report = logs.map(rowCost).sum;
```

<!-- EXAMPLES.md:845 layer L16: ring L3, word L16 (@commutative), label none -->
```zed
// [d4*] sec:property_tracking, sec:reduction, sec:corner_cases — a user-written monoid: mean and variance in one parallel pass
struct Moments { n: int, sum: rat, sumSq: rat }
moment(positional x: rat) = Moments(n: 1, sum: x, sumSq: x * x);
@associative @commutative combine(positional a: Moments, positional b: Moments) = Moments(n: a.n + b.n, sum: a.sum + b.sum, sumSq: a.sumSq + b.sumSq);
m        = xs.map(moment) >< combine else Moments(n: 0, sum: 0r, sumSq: 0r);   // xs : [rat]; the claim is Derived — a tupling of `+` monoids — so combine-as-arrives is licensed
mean     = m.sum / rat(m.n);                                                    // rat | #divByZero: zero exactly when xs was empty
variance = m.sumSq / rat(m.n) - mean * mean;                                    // both operands fail together with the same atom, so the merge is #divByZero again (sec:failure)
```

<!-- EXAMPLES.md:857 layer L15: ring L10, word L15 (@ensure), label none -->
```zed
// [d4] sec:domains, sec:kernel (law 16) — `@ensure`: the refinement is deleted by the preimage or the build fails; never a hidden run-time check
@ensure scaledOdd(x: int[0..=100]) = (x * 2 + 1).refine(v -> v < 100);   // ✗ int[0..=100] does not entail the preimage; the menu prints `x: int[0..=49]`
@ensure odd(positional x) = (x * 2 + 1).refine(v -> v < 100);              // inferred: x <= 49 — the obligation moves to the callers
a = odd(12);                                                              // 25: a literal is a static frontier, decided here
b = odd(60);                                                              // ✗ 60 is outside x <= 49; the call is rejected, and nothing runs to find out
```

<!-- EXAMPLES.md:865 layer L15: ring L15, word L15 (byInduction), label none -->
```zed
// [d4] sec:verification — a law is boolean Zed over binders, graded by the discharge ladder; a proof is a value the checker checks
law doubleIsSum(x: int) = double(x) == x + x;                                           // Proved(#domain): the abelian normal form (rung 2)
law clampInRange(v: int, lo: int, hi: int where lo <= hi) = clamp(v, lo, hi) in lo..=hi; // Proved(#domain): exact min/max transfer; `where` narrows a binder as in a `for` head
law nextCycles(c: Color) = next(next(next(c))) == c;                                    // CheckedExhaustive(Color): three cases, run (rung 1) — Color and next: section 11
mirror(positional t: Tree) = match t { #leaf -> #leaf, Node(l:, v:, r:) -> Node(l: mirror(r), v:, r: mirror(l)) };  // Tree, Node, size: section 15
law mirrorKeepsSize(t: Tree) = size(mirror(t)) == size(t)                              // the `proof` clause ends the declaration, as `test` does
  proof { byInduction(t) }                                                              // structural induction on Tree; `ih` is bound in the step; the tactic is compile-time Zed returning a Proof
                                                                                        // law 21 proves it with no induction: t -> size(mirror(t)) satisfies size's fold equation, + being commutative
law sortIdempotent(xs: [int]) = xs.sort(asc x -> x).sort(asc x -> x) == xs.sort(asc x -> x);   // Obligated: below proof grade — reported, property-tested, and no rewrite is licensed by it
```

<!-- EXAMPLES.md:877 layer L15: ring L15, word L15 (@invariant), label none -->
```zed
// [d4] sec:verification, sec:generations — a loop is a state machine: `@invariant` is loop induction, and the reachable set is a fixpoint the compiler evaluates ([lib] image)
amt(positional t: int) = withdrawals[t] else 0;                                                 // withdrawals : [int]; past the end nothing is withdrawn
account = loop t {
  @invariant(balance >= 0) balance' = if amt(t) <= balance { balance - amt(t) } else { balance }   with balance = 0;
  until t + 1 >= withdrawals::len;
};
law neverNegative(t: int[0..<account::len]) = account::frames[t].balance >= 0;   // what @invariant asserts, as a law over the history: init, then p(s).implies(p(step(s))) — an `until` step runs before its guard is read

type Lamp = #green | #yellow | #red;
type Cmd  = #tick | #fault;
advance(positional l: Lamp, positional c: Cmd) = if c == #fault { #red } else { match l { #green -> #yellow, #yellow -> #red, #red -> #green } };
reachable = loop { R' = R.union(R.flatMap(l -> [advance(l, #tick), advance(l, #fault)]).image) with R = { #red }; };   // monotone, so no guard; finite, so computed at compile time
law faultStops(l: Lamp) = (l in reachable.R).implies(advance(l, #fault) == #red);    // CheckedExhaustive(Lamp): the model check is partial evaluation; a refutation would carry the (state, command) trace
```

<!-- EXAMPLES.md:897 layer L20: ring L20, word L10 (refine), label none -->
```zed
// [d4] sec:domains
type Port  = int[1..=65535];
type Name  = String[len 1..=80];
type Small(K, V) = (K -> V)[card <= 10];
type Ident = String matching grammar { alpha (alpha | digit)* };
p: Port = 8080;
q: Port = 70000;                          // ✗ 70000 is not in int[1..=65535]
n = int(input);                           // int | #invalid
p2 = n?.refine(v -> v in 1..=65535);      // int | #invalid, and the refinement is what the checker keeps
```

<!-- EXAMPLES.md:909 layer L10: ring L10, word none, label none -->
```zed
// [d4] sec:type_language (m[k] row) — indexing is total on a matching domain
grid: int[0..<w] -> int[0..<h] -> Cell = …;
cell = grid[x][y];                        // Cell when x : int[0..<w] and y : int[0..<h]; otherwise | #notFound
all  = for x -> y -> _ in grid { grid[x][y] };   // total, by construction: the binder names grid's own keys
```

<!-- EXAMPLES.md:918 layer L13: ring L7, word L13 (taint), label none, documentation notation -->
```zed
// [d4] sec:tour_grammar, sec:facets
v = 3.0 with units("m/s");
t = 2.0 with units("s");
d = v * t;                                 // f64 with units("m")
bad = v + t;                               // ✗ m/s + s
u = d::units;
exec : (Db, String with taint(#clean)) -> Rows | #sqlError   // a sink's signature, shown as a type — no ';'
q = exec(db, "select …" ++ userInput);     // ✗ taint flows through ++
```

<!-- EXAMPLES.md:931 layer L12: ring L7, word L12 (parity), label none -->
```zed
// [d4*] sec:checking_in_zed — `parity` is the evidence facet declared there
half(positional x: int with parity(#even)) = x div 2;
g(n: int with parity(#odd)) = half(n + n);            // ✓ #odd + #odd is #even, and #add's soundness law is Proved
k(n: int with parity(#odd), m: int) = half(n * m);    // m carries no parity fact, so #mul gives #either: the demand stays the run-time test holds(#even, n * m), and k returns int | #invalid
seven = 7 with parity(#odd);                          // attaching a fact is an obligation: holds(#odd, 7) runs at build
```

<!-- EXAMPLES.md:941 layer L15: ring L3, word L15 (@ensure), label none -->
```zed
// [lib] sec:checking_in_zed, sec:staging, sec:domains — `format` is a library guess
squares = (0..<256).map(i -> i * i);                     // computed at build, residualized as a literal
@ensure line = format("{} scored {}", [name, score]);   // the spec is static: parsed at build, the residual is concatenation
@ensure oops = format("{} scored {}", [name]);          // ✗ at build, with the library's message: two holes, one argument
```

<!-- EXAMPLES.md:952 layer L20: ring L20, word L20 (serialize), label none -->
```zed
// [d4] sec:tour_grammar
struct KeyVal  grammar { key: Ident ":" value: Json }
struct JsonObj grammar { "{" entries: KeyVal sep "," "}" }
type Json = JsonObj | JsonArr | JsonStr | JsonNum | #true | #false | #null;
cfg = Json.parse(bytes);                  // Json | #syntaxError(pos: int)
out = cfg?.serialize;
```

<!-- EXAMPLES.md:961 layer L20: ring L20, word L3 (map), label none -->
```zed
// [d4*] sec:tour_grammar, sec:tour_methods — an arithmetic language: grammar, then meaning by method
struct Sum   grammar { terms: Prod sep "+" }
struct Prod  grammar { factors: Atom sep "*" }
struct Paren grammar { "(" inner: Sum ")" }
type Number = String matching grammar { digit digit* };
type Atom   = Number | Paren;
Sum.eval    = terms.map(t -> t.eval).sum;
Prod.eval   = factors.map(f -> f.eval) >< (*);
Paren.eval  = inner.eval;
Number.eval = int(this) else 0;            // the grammar proved the digits; int is unbounded, and the else covers int()'s failure atom
value = Sum.parse("2*(3+4)")?.eval;        // 14, or #syntaxError
```

<!-- EXAMPLES.md:977 layer L7: ring L7, word L5 (patch), label none -->
```zed
// [d4*] sec:generations — a ledger: transactions are edits, the loop is the account book
struct Account { bal: rat }
type Tx = #deposit(id: AccountId, amt: rat) | #withdraw(id: AccountId, amt: rat);
edits: (Tx) -> AccountId ->? Edit(Account);
edits(positional tx) = match tx {
  #deposit(id:, amt:)  -> { id -> #update(a -> a with { bal = a.bal + amt }) },
  #withdraw(id:, amt:) -> { id -> #update(a -> a with { bal = a.bal - amt }) },
};
book = loop t {
  accts' = accts.patch(edits(txs[t])) with accts = opening;
  while t in txs::domain;
};
closing = book.accts;
```

<!-- EXAMPLES.md:993 layer L6: ring L6, word L6 (::frames), label none -->
```zed
// [d4] sec:generations — a state machine
type Light = #green | #yellow | #red;
next(positional l: Light) = match l { #green -> #yellow, #yellow -> #red, #red -> #green };
lights = loop t { l' = next(l) with l = #red; until t == 10; };
trace  = lights::frames.map(f -> f.l);    // [Light]
```

<!-- EXAMPLES.md:1001 layer L10: ring L10, word L3 (where), label none -->
```zed
// [d4*] sec:generations, sec:tour_loops — Conway's life on a torus
alive(positional cells, positional p) -> bool {
  x, y = p;
  ns = for d in [(-1,-1), (-1,0), (-1,1), (0,-1), (0,1), (1,-1), (1,0), (1,1)] {
    dx, dy = d;
    cells[((x + dx) mod w, (y + dy) mod h)] else false
  };
  n = ns.where(b -> b).count;
  if (cells[p] else false) { (n == 2) || (n == 3) } else { n == 3 }
}
life = loop t {
  cells' = for p -> _ in cells { alive(cells, p) } with cells = seed;
  until t == 100;
};
```

<!-- EXAMPLES.md:1018 layer L5: ring L3, word L5 (maxBy), label none -->
```zed
// [d4*] sec:grouping, sec:reduction — log analytics
struct Req { path: String, status: int, ms: int }
byPath  = reqs.group(r -> r.path);
errRate = byPath.map(rs -> f64(rs.where(r -> r.status >= 500).count) / f64(rs::card));
slowest = byPath.map(rs -> rs.map(r -> r.ms).max).maxBy(m -> m);      // (ms ->? (Path -> ms)) | #none; .max is exact: groups are nonempty
```

<!-- EXAMPLES.md:1026 layer L21: ring L7, word L21 (store), label none -->
```zed
// [d4*] sec:generations, sec:ports — a todo list with a store, driven by commands
struct Todo { title: String, done: bool }
todos: TodoId ->? Todo with store(kv(endpoint));
main(cmds: Stream(Cmd)) -> (out: Lines) {
  run = loop t {
    todos' = todos.patch(toEdits(cmds[t]));
    while t in cmds::domain;
  };
  out <- run::frames.map(f -> "${f.todos::card} items");
}
```

<!-- EXAMPLES.md:1041 layer L7: ring L7, word L7 (reducer), label none -->
```zed
// [d4] sec:generations, sec:push_pull (hist), sec:tour_loops (cdf), sec:power (edit distance, with cost(a[i], b[j]) inlined as 0/1)
hist: int ->? int with reducer((+));                                // the accumulator names its reducer, so many sites may push
for s in words { hist[s.len] <- 1; };                               // one keyed push per word; + arbitrates the overlap
histB = words.group(s -> s.len).count;                              // the same histogram as a group-by
cdf[i in 0..=maxLen] = cdf[i-1] + (hist[i] else 0) with cdf[-1] = 0;  // hist is partial: default the gaps
d[i][j] = if a[i] == b[j] { d[i-1][j-1] } else { 1 + min(d[i-1][j], d[i][j-1], d[i-1][j-1]) }
  with d[-1][j in -1..<b::len] = j + 1, d[i in 0..][-1] = i + 1;
```

<!-- EXAMPLES.md:1051 layer L8: ring L8, word L3 (where), label none -->
```zed
// [d4*] sec:tour_loops, sec:joins — two-sum is a self-join on the complementary value
byVal = xs as (i -> v) into (v -> i -> _);                                       // int ->? set of positions
pairs = for i -> v in xs where (target - v) in byVal::domain { (i, byVal[target - v].where(j -> j != i)) };   // a position never pairs with itself; the binder names the position and the value
```

<!-- EXAMPLES.md:1057 layer L3: ring L3, word L3 (where), label none -->
```zed
// [d4] sec:tour_collections — primes by trial division; a range is a domain
isPrime(positional k) = k >= 2 && (2..<k).where(d -> (d * d) <= k && (k mod d) == 0).count == 0;
primes = (2..=n).where(isPrime);
```

<!-- EXAMPLES.md:1063 layer L5: ring L1, word L5 (first), label none -->
```zed
// [d4*] sec:tour_loops — run-length encoding: chunks are nonempty, so first is exact
rle = xs.chunkBy(x -> x).map(c -> (c.first, c.count));
```

<!-- EXAMPLES.md:1068 layer L10: ring L10, word none, label none -->
```zed
// [d4*] sec:failure, sec:type_language — binary search over xs sorted ascending (on unsorted input it can return #none for a t that is present), with the miss the type insists on
bsearch(xs: [int], t: int) -> int | #none {
  go(positional lo, positional hi) -> int | #none {
    if lo > hi { #none }
    else {
      mid = (lo + hi) div 2;
      match xs[mid] {
        #notFound -> #none,                          // unreachable by the invariant, but the type asks
        v -> if v == t { mid } else if v < t { go(mid + 1, hi) } else { go(lo, mid - 1) },
      }
    }
  }
  go(0, xs::len - 1)
}
```

<!-- EXAMPLES.md:1085 layer L5: ring L3, word L5 (first), label none -->
```zed
// [d4] sec:kernel (law 22), sec:optimizer — the same search as a query: the least index whose entry is at least t. When the xs a call passes is a sorted view ascending (a .sort(asc …) result is one, and specialization carries that into the body, sec:order), i -> xs[i] >= t is monotone along the range, and the plan is bisection, O(log n); without it the plan is a scan with the same result
lowerBound(positional xs: [int], positional t: int) = (0..<xs::len).where(i -> xs[i] >= t).first;   // int[0..<n] | #none, n = xs::len: #none when every entry is below t
find(xs: [int], t: int) = match lowerBound(xs, t) { #none -> #none, i -> if xs[i] == t { i } else { #none } };   // i : int[0..<n], so the lookup cannot miss
```

<!-- EXAMPLES.md:1091 layer L10: ring L10, word none, label none -->
```zed
// [d4] sec:tour_joins, sec:remap_law — matrices are two-level morphisms
type Mat(n, m) = int[0..<n] -> int[0..<m] -> f64;
ab  = (a, b) into (r -> k -> c >< (+) -> a[r][c] * b[c][k]);
at  = a as (r -> c -> v) into (c -> r -> v);                   // transpose: a repack
eye = for i in 0..<n { for j in 0..<n { if i == j { 1.0 } else { 0.0 } } };
```

<!-- EXAMPLES.md:1099 layer L6: ring L5, word L5 (sort), label L6 -->
```zed
// [d4*] sec:remap_law, sec:power — a shuffle is a sort by a random key; Fisher–Yates is a serial swap loop, the rank pass is not
// layer L6
order    = (0..<xs::len).sort(asc i -> rnd[i]);   // [int]: a permutation — rnd is the recurrence of section 14, and a full-period generator never repeats a key
shuffled = order.map(i -> xs[i]);                 // [T]: xs in that order
sample   = shuffled.slice(0, k);                  // [lib] k of n without replacement; sort pruning makes the sort a top-k selection (sec:optimizer)
```
