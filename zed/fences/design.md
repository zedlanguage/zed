<!-- The `zed` fences of the spec's DESIGN.md, copied by the sync tool: do not edit. -->

<!-- DESIGN.md:197 layer L8: ring L8, word none, label none, documentation notation; section [sec:remap_law] 1 -->
```zed
src as (sourceKeypathPattern) into (outputKeypathPattern -> leaf)
```

<!-- DESIGN.md:220 layer L8: ring L8, word none, label none, documentation notation; section [sec:remap_law] 2 -->
```zed
   as (k1 -> k2 -> v) into (k2 -> k1 -> v)        // transpose levels
   as (k1 -> k2 -> v) into ((k1, k2) -> v)        // flatten to a tuple key
   as (k -> v)        into (k + 1 -> v)           // bijective key transform
```

<!-- DESIGN.md:227 layer L8: ring L8, word none, label none, documentation notation; section [sec:remap_law] 3 -->
```zed
   as (k1 -> k2 -> v) into (k1 -> (k2, v) -> v)   // key widened with the value: still injective
   as (k -> v)        into ((k, f(k)) -> v)       // key widened with derived data
```

<!-- DESIGN.md:232 layer L8: ring L8, word none, label none, documentation notation; section [sec:remap_law] 4 -->
```zed
   as (k1 -> k2 -> v) into (k1 -> k2 -> _)        // keep the key structure, discard values:
                                                  //   result type  K1 -> (K2 -> K2)   (set-leaf)
   as (k1 -> k2 -> v) into (k1 -> k2)             // sugar for the same (trailing source-key = truncate)
```

<!-- DESIGN.md:243 layer L8: ring L8, word none, label none, documentation notation; section [sec:remap_law] 5 -->
```zed
as (region -> day -> sku -> r) into (region -> day -> r)       // ✗ Collision: compile error
```

<!-- DESIGN.md:264 layer L8: ring L8, word none, label none, documentation notation; section [sec:remap_law] 6 -->
```zed
as (region -> day -> sku -> r) into (region -> day -> sku >< (+) -> r)    // collapse the sku level by explicit reduction
```

<!-- DESIGN.md:274 layer L8: ring L8, word none, label none; section [sec:remap_law] 7 -->
```zed
byScore = scores into (desc score -> name -> score);   // scores : name -> score; adjoin a rank level ordered by score
```

<!-- DESIGN.md:289 layer L8: ring L8, word L4 (rekey), label none; section [sec:grouping] 1 -->
```zed
byLower = words into (w.lower -> i -> w);   // words : i -> w; residue `i` written — injective, one level deeper
// byLower = words.group(w -> w.lower);     // the same program: the word `group` declares the same deeper type, Lower ->? (i -> w)
byId    = users.rekey(u -> u.id);         // flat claim: error unless id-uniqueness is witnessed
```

<!-- DESIGN.md:353 layer L8: ring L8, word none, label none; section [sec:joins] 1 -->
```zed
  matmul(positional a: (r -> c -> f64), positional b: (c -> k -> f64)) =  // one shared inner domain c; the float
    (a, b) into (r -> k -> c >< (+) -> a[r][c] * b[c][k]); //   the float `+` folds on the canonical tree over `c`'s order
                                                           //   (sec:order, sec:reduction)
```

<!-- DESIGN.md:361 layer L8: ring L8, word none, label none; section [sec:joins] 2 -->
```zed
  r1 = (a, b, c) into (a || b || c -> v);      // v: (f64 | #none, Utf8String | #none, bool | #none)
  r2 = (a, b, c) into (a && b && c -> v);      // v: (f64, Utf8String, bool)
  r3 = (a, b, c) into (a && ?b && ?c -> v);    // v: (f64, Utf8String | #none, bool | #none), keys of a
  r4 = (a, b, c) into (a && !b && c -> v);     // v: (f64, bool), keys in a and c, not in b
  r5 = (a, b, c) into (a && ?(b && ?c) -> v);  // v: (f64, (Utf8String, bool | #none) | #none), keys of a
  ab = (a, b) into (a || b -> v);
  r6 = (ab, c) into (ab || c -> v);            // v: ((f64 | #none, Utf8String | #none) | #none, bool | #none)
```

<!-- DESIGN.md:482 layer L6: ring L6, word none, label none; section [sec:generations] 1 -->
```zed
sim = loop {
  initial pos = p0;                                    // the sentinel values, before step 0
  initial vel = v0;
  pos' = pos + vel * dt;                               // x' means the frame being built; bare x the previous
  vel' = vel + a(pos) * dt;
  until pos'.x > bound;
};
```

<!-- DESIGN.md:509 layer L6: ring L6, word none, label none; section [sec:generations] 2 -->
```zed
x[i in 0..<warm]  = coldStart(i);         // piecewise definition: phase 1
x[i in warm..<n]  = anneal(x[i-1]);       // phase 2 — reads across the seam legally
```

<!-- DESIGN.md:548 layer L10: ring L10, word none, label none, documentation notation; section [sec:failure] 1 -->
```zed
(div) : ((int, int \ 0) -> int) & ((int, 0) -> #divByZero)
```

<!-- DESIGN.md:601 layer L1: ring L1, word L1 (MainArgs), label none; section [sec:ports] 1 -->
```zed
  // exits with 0: the body exports nothing
  main(m: MainArgs) {
    m.stdout <- "Hello, world!";
  }

  // exits with 1 when the first argument is "fail", and with 0 otherwise
  main(m: MainArgs) -> int {
    m.stdout <- "checked";
    if (m.args[0] else "") == "fail" { 1 } else { 0 }
  }
```

<!-- DESIGN.md:630 layer L12: ring L7, word L12 (units), label none; section [sec:ports] 2 -->
```zed
  // with the argument 3 writes 256r; with 40 the power needs 128 GiB, more than the 1 GiB the run may hold,
  // so the run stops at `2r^(2^k)` with exit status 3; it also stops after 60 s of processor time or 5 minutes
  @limits(memory: 1 with units("GiB"), cpu: 60 with units("s"))
  @timeout(5 with units("min"))
  main(m: MainArgs) {
    k = int(m.args[0] else "") else 0;
    m.stdout <- String(if k >= 0 { 2r^(2^k) } else { 0r }) else "";
  }

  // rejected at compile time: `b ^ (2^20)` needs at least 2^20 * 64 bits, 8 MiB, and the run may hold 1 MiB
  @limits(memory: 1 with units("MiB"))
  main(m: MainArgs) {
    b = 2^64 + 13;
    m.stdout <- String(b ^ (2^20));
  }
```

<!-- DESIGN.md:662 layer L7: ring L3, word L7 (spawn), label none; section [sec:ports] 3 -->
```zed
  // runs git with two words and no shell; a failure to start, an exit code and a signal are each handled
  main(m: MainArgs) -> int {
    r = run(["git", "status", "--short"]);
    match r {
      #ioError(op:, path:, why:) -> { m.stderr <- "git did not start: ${why}"; 2 },
      done -> match done.status {
        #ok -> { m.stdout <- done.stdout; 0 },
        #exit(code:) -> { m.stderr <- done.stderr; code },
        _ -> 1,
      },
    }
  }

  // sorts standard input through `sort -u`: the last push into p.stdin closes the child's input,
  // reading p.stdout to its end waits for the child, and its stderr, never read, passes through
  main(m: MainArgs) {
    p = spawn(["sort", "-u"]);
    p.stdin <- m.stdin.map(l -> l else "");
    m.stdout <- p.stdout.map(l -> l else "");
  }
```

<!-- DESIGN.md:689 layer L7: ring L3, word L7 (run), label none; section [sec:ports] 4 -->
```zed
  // compresses every file named on the command line; the runs are not ordered, so they may overlap
  main(m: MainArgs) {
    runs = m.args.map(f -> run(["gzip", "--keep", "--", f], unconsumedStderr: #suppress).status);
    m.stdout <- runs.map(s -> match s { #ok -> "compressed", _ -> "gzip failed" });
  }
```

<!-- DESIGN.md:720 layer L21: ring L7, word L21 (store), label none; section [sec:ports] 5 -->
```zed
  orders: Utf8String ->? { total: rat, note: Utf8String | #none }
    with store(postgres(dbUrl, table: "orders", schema: sql("db/orders.sql")));
  owed(positional id: Utf8String) -> rat = orders[id]?.total else 0r
    test with orders = { "7" -> { total: 12r, note: #none } } { "7" -> 12r, "8" -> 0r }

  late(positional deadline: Instant) -> bool = now().s > deadline.s
    test with now = () -> Instant(s: 3600r) { Instant(s: 3599r) -> true, Instant(s: 3600r) -> false }
```

<!-- DESIGN.md:753 layer L22: ring L22, word L7 (Stream), label none; section [sec:codecs] 1 -->
```zed
type DecodeFailure = #badEncoding(at: int, layer: Utf8String, why: Utf8String)
  | #syntaxError(pos: int, expected: [Utf8String], open: [#open(rule: Utf8String, pos: int)])
  | #parseError(pos: int, expected: [Utf8String], open: [#open(rule: Utf8String, pos: int)], msg: Utf8String);

// any layer: a lossy one, such as a video codec, promises no round trip
type LossyCodec(positional W, positional V) = {
  name: Utf8String,
  decode: (Stream(W | DecodeFailure)) -> Stream(V | DecodeFailure),
  encode: (Stream(V)) -> Stream(W),
};

// a layer that loses nothing: what it writes, it reads back
interface Codec(positional W, positional V) {
  name: Utf8String,
  decode: (Stream(W | DecodeFailure)) -> Stream(V | DecodeFailure),
  encode: (Stream(V)) -> Stream(W),
  law roundTrip(vs: Stream(V)) = decode(encode(vs)) == vs,
}

// a layer with one encoding per value: what it reads, it writes back byte for byte
interface CanonicalCodec(positional W, positional V) {
  import Codec(W, V),
  law canonical(ws: Stream(W), vs: Stream(V)) = (decode(ws) == vs).implies(encode(vs) == ws),
}
```

<!-- DESIGN.md:784 layer L22: ring L22, word L10 (Codec), label none; section [sec:codecs] 2 -->
```zed
then(positional a: Codec(A, B), positional b: Codec(B, C)) -> Codec(A, C) = {
  name: b.name,
  decode: ws -> b.decode(a.decode(ws)),
  encode: vs -> a.encode(b.encode(vs)),
};

law thenRoundTrip(a: Codec(A, B), b: Codec(B, C), vs: Stream(C)) =
  b.decode(a.decode(a.encode(b.encode(vs)))) == vs
proof {
  b.decode(a.decode(a.encode(b.encode(vs))))
    == b.decode(b.encode(vs))
    == vs
}
```

<!-- DESIGN.md:804 layer L7: ring L3, word L7 (::bytes), label none; section [sec:codecs] 3 -->
```zed
// the bytes of standard input, counted; nothing is decoded
main(m: MainArgs) {
  m.stdout <- "${m.stdin::bytes::len}";     // "1000 B" for 1000 bytes: the length is in B
}
```

<!-- DESIGN.md:811 layer L20: ring L3, word L20 (json), label none; section [sec:codecs] 4 -->
```zed
// standard input as JSON values, one Event each, whitespace between them allowed;
// a value that does not parse is written as a line saying so
struct Event { name: Utf8String, at: int }

main(m: MainArgs) {
  events = m.stdin::bytes.via(utf8Text().then(json(Event)));
  m.stdout <- events.map(e -> e.name else "(a value that did not parse)");
}
```

<!-- DESIGN.md:826 layer L10: ring L10, word L7 (utf8Text), label none; section [sec:codecs] 5 -->
```zed
// what a line read through lines() can be: no line feed and no carriage return
type Line = (s: Utf8String where !s.contains("\n") && !s.contains("\r"));
type RawLine = (s: Utf8String where !s.contains("\n"));
type Lines = Stream(Utf8String);

textLines = utf8Text().then(lines());
```

<!-- DESIGN.md:874 layer L10: ring L3, word L10 (CanonicalCodec), label none; section [sec:codecs] 6 -->
```zed
// a user layer: each byte shifted by k, as some old formats hide their data
shifted(k: u8) -> CanonicalCodec(u8, u8) = {
  name: "shifted",
  decode: ws -> ws.map(b -> (b + 256 - k) mod 256),
  encode: vs -> vs.map(b -> (b + k) mod 256),
};

// adapting a layer: lines read with the spaces around them dropped; lossy, so typed as such
trimmed(positional c: LossyCodec(W, Line)) -> LossyCodec(W, Line) = {
  name: "trimmed",
  decode: ws -> c.decode(ws).map(l -> l.trim),
  encode: c.encode,
};

main(m: MainArgs) {
  // inserted below the text layers, and the text layers kept
  m.stdout <- m.stdin::bytes.via(shifted(k: 13).then(textLines)).map(l -> l else "");
}
```

<!-- DESIGN.md:907 layer L20: ring L7, word L20 (records), label none; section [sec:codecs] 7 -->
```zed
// a C array of samples from a foreign library, written to a file in the C layout
@foreign struct Sample { t: u64, value: f64 }
@foreign("sensor", "sensor_free") @nonblocking freeSamples: (p: Ptr([Sample] with length(1024))) -> #ok;
@foreign("sensor", "sensor_read") @blocking readSamples: (count: i32) -> Ptr([Sample] with length(1024)) with release(freeSamples);

main(m: MainArgs) {
  fs = main::files;
  samples = readSamples(count: 1024) else [];          // read in place, freed after its last use
  fs::bytes["samples.bin"] <- records(Sample).encode(samples);
  m.stdout <- "${samples::len} samples written";
}
```

<!-- DESIGN.md:921 layer L20: ring L3, word L20 (records), label none; section [sec:codecs] 8 -->
```zed
// a later run reads them back; each record is a view of the file's bytes
main(m: MainArgs) {
  back = (main::files::bytes["samples.bin"] else []).via(records(Sample));   // Sample | DecodeFailure per record
  m.stdout <- "${back::len} samples read";
}
```

<!-- DESIGN.md:1039 layer L3: ring L3, word L1 (Utf8String), label none; section [sec:level_names] 1 -->
```zed
// region -> day -> sku -> quantity sold
type Sales0 = Utf8String ->? [Utf8String ->? int];
```

<!-- DESIGN.md:1046 layer L10: ring L10, word L7 (names), label none; section [sec:level_names] 2 -->
```zed
type Sales = Utf8String ->? [Utf8String ->? int] with names("region", "day", "sku", "quantitySold");
sales: Sales = { "east" -> [{ "B7" -> 5 }], "west" -> [{ "A12" -> 3, "B7" -> 1 }, { "A12" -> 2 }] };
```

<!-- DESIGN.md:1111 layer L10: ring L10, word L7 (names), label none; section [sec:level_names] 3 -->
```zed
lookupOr(positional m: K ->? V with names("key", "value"), positional k: K, positional d: V) -> V = m[k] else d;

stock: Utf8String ->? int with names("sku", "count") = { "A12" -> 3 };
n = lookupOr(stock, "B7", 0);                  // V is int; n is 0

daily: Utf8String ->? ((day: int) ->? int) with names("store", "_", "sold") = { "s1" -> { 1 -> 4 } };
s = lookupOr(daily, "s1", { 0 -> 0 });         // V is (day: int) ->? int; s is { 1 -> 4 }
```

<!-- DESIGN.md:1123 layer L10: ring L10, word L7 (names), label none; section [sec:level_names] 4 -->
```zed
relabel(positional m: K ->? V) -> K ->? V with names("key", "value") = m;

daily: Utf8String ->? ((day: int) ->? int) with names("store", "_", "sold") = { "s1" -> { 1 -> 4, 2 -> 6 }, "s2" -> { 1 -> 5 } };
r = relabel(daily);                               // V is (day: int) ->? int, with the names ("day", "sold")
// r::names is ("key", "day", "sold"), and `value` names each inner map, { 1 -> 4, 2 -> 6 } at "s1"
d1 = r[day: 1];                                   // { "s1" -> 4, "s2" -> 5 }; d1::names is ("key", "sold")
byDay = r into (day -> key -> sold);              // { 1 -> { "s1" -> 4, "s2" -> 5 }, 2 -> { "s1" -> 6 } }
whole = r into (key -> value);                    // r itself: `value` binds the inner map
targets: (day: int) ->? int with names("day", "target") = { 1 -> 5, 2 -> 5 };
vs = (r, targets) into (key -> day -> (pair: (sold, target)));
// vs is { "s1" -> { 1 -> (4, 5), 2 -> (6, 5) }, "s2" -> { 1 -> (5, 5) } }
```

<!-- DESIGN.md:1194 layer L10: ring L10, word L7 (names), label none; section [sec:level_names] 5 -->
```zed
   totals = sales into (region -> day -> sku >< (+) -> quantitySold);
   // totals is { "east" -> [5], "west" -> [4, 2] }; totals::names is ("region", "day", "sum_quantitySold")
   labels: Utf8String ->? [Utf8String] with names("sku", "pos", "label") = { "A12" -> ["red", "small"] };
   joined = labels into (sku -> pos >< (++) -> label);
   // joined is { "A12" -> "redsmall" }; joined::names is ("sku", "concat_label")
```

<!-- DESIGN.md:1204 layer L8: ring L8, word none, label none; section [sec:level_names] 6 -->
```zed
   floof(positional a: int, positional b: int) -> int = a + b;
   f = sales into (region -> day -> sku >< floof -> quantitySold);
   // f is { "east" -> [5], "west" -> [4, 2] }; f::names is ("region", "day", "floof_quantitySold")
```

<!-- DESIGN.md:1212 layer L8: ring L8, word none, label none; section [sec:level_names] 7 -->
```zed
   g = sales into (region -> day -> sku >< ((a, b) -> a + b) -> quantitySold);
   // g::names is ("region", "day", "reduce_quantitySold")
   import tools.stats;
   h = sales into (region -> day -> sku >< stats.floof -> quantitySold);
   // h::names is ("region", "day", "reduce_quantitySold")
```

<!-- DESIGN.md:1238 layer L10: ring L10, word L7 (names), label none; section [sec:level_names] 8 -->
```zed
prices: (sku: Utf8String) ->? f64 with names("sku", "price") = { "A12" -> 2.5, "B7" -> 4.0 };
lines = (sales, prices) into (region -> day -> sku -> (line: (quantitySold, price)));
// lines is { "east" -> [{ "B7" -> (5, 4.0) }], "west" -> [{ "A12" -> (3, 2.5), "B7" -> (1, 4.0) }, { "A12" -> (2, 2.5) }] }
// lines::names is ("region", "day", "sku", "line")
```

<!-- DESIGN.md:1249 layer L8: ring L8, word none, label none; section [sec:level_names] 9 -->
```zed
a12 = sales[sku: "A12"];
// a12 is { "east" -> [#notFound], "west" -> [3, 2] }
// a12::names is ("region", "day", "quantitySold")
```

<!-- DESIGN.md:1331 layer L10: ring L10, word L1 (Utf8String), label none; section [sec:constraints] 1 -->
```zed
type Small = (x: int where x * x < 100);                    // nonlinear
type Even  = (n: int where n mod 2 == 0);                   // a residue
type Prime = (p: int[2..] where isPrime(p));                // a predicate no domain models
type Short = (s: Utf8String where s.len < 100);                 // a length
area(a: int[1..], b: int[1..] where a * b <= 99) -> int = a * b;   // a relation
```

<!-- DESIGN.md:1349 layer L6: ring L3, word L6 (Reduction), label none; section [sec:constraints] 2 -->
```zed
parityFromIntervals = Reduction(of: parity, reads: [intervals],
    reduce: (e, s) -> if s.of(intervals).isPoint { if s.of(intervals).lo mod 2 == 0 { #even } else { #odd } } else { e });
intervalsFromParity = Reduction(of: intervals, reads: [parity],
    reduce: (e, s) -> if s.of(parity) == #even { e.roundInwardToEven } else { e });
```

<!-- DESIGN.md:1403 layer L10: ring L10, word L6 (Ast), label none; section [sec:constraints] 3 -->
```zed
type Bound = int | Ast | #unbounded;                         // an affine bound is an expression over names in scope
struct Interval   { min: Bound, max: Bound }
struct Congruence { modulus: int[0..], residue: int }        // residue in 0..<modulus when modulus > 0
struct FloatClass { min: f64, max: f64, nonNaN: bool, width: #f16 | #bf16 | #f32 | #f64 }   // bounds in totalOrder, exact in f64 at every width; nonNaN false: not known
struct Constraints(positional V) {
  subject:    Ast,                                         // the name that stands for the value in every Ast below
  interval:   Interval | [Interval] | #none,                 // a list for a finite union: sorted, disjoint, not adjacent
  congruence: Congruence | #none,
  values:     [V] | #unknown,                                // the finite set, where one is known
  length:     Interval | #none,                              // strings and lists; ::card for morphisms
  floats:     FloatClass | #none,
  relations:  [Ast],                                         // the linear relations that name x
  written:    [Ast],                                         // the constraints as written
}
```

<!-- DESIGN.md:1473 layer L2: ring L2, word none, label none; section [sec:units] 1 -->
```zed
import geometry.shapes;               // qualified: shapes.area(s: c)
import geometry.shapes as g;          // aliased:   g.area(s: c)
import geometry.shapes.{area, Rect};  // selective: area(s: c), Rect(…)
```

<!-- DESIGN.md:1540 layer L20: ring L20, word L1 (Utf8String), label none; section [sec:facets] 1 -->
```zed
type Nonzero = Utf8String matching grammar { "0"* ("1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9") digit* };
type UnitName = Utf8String matching grammar { alpha (alpha | digit | "_")* | "°" alpha* | "%" | "′" | "″" | "'" | "\"" };
type UnitKind = Utf8String matching grammar { "#" alpha (alpha | digit | "_")* };
type UnitPower = Utf8String matching grammar { "-"? digit+ | "(" "-"? digit+ "/" Nonzero ")" };
type UnitFactor = Utf8String matching grammar { UnitName ("^" UnitPower)? };
type UnitProduct = Utf8String matching grammar { UnitFactor sep (" " | "*" | "·") };
type UnitLinear = Utf8String matching grammar { (UnitProduct | "1") ("/" (UnitFactor | "(" UnitProduct ")"))? };
type UnitLog = Utf8String matching grammar { ("log10" | "log2" | "log") "(" UnitLinear ")" };
type UnitText = Utf8String matching grammar { UnitLog | UnitLinear (" " UnitKind)? | UnitKind | "" };
// accepted: "m^2 s^-1", "kg m/s^2", "J/(kg K)", "m^(3/2)", "1/s", "", "µm", "Å", "kΩ", "%", "°C", "N m #torque", "#ratio", "log(m)", "log10(mol/L)", "log2(1/s)", "log(1)", "char16"
// rejected: "J/kg K", "m^1.5", "m / s", "m^(3/0)", "m #", "N m #torque #energy", "log(m) s", "log(N m #torque)", "ln(m)"
```

<!-- DESIGN.md:1558 layer L12: ring L12, word L12 (UnitText), label none; section [sec:facets] 2 -->
```zed
struct UnitDef {
  name: UnitName,
  unit: UnitText | #base,
  factor: rat = 1r,
  piPower: int = 0,
  offset: rat = 0r,
  ascii: UnitName | #none = #none,
  prefixes: [UnitName] = [],
  law positive() = factor > 0r,
  law baseIsOne() = (unit == #base).implies(factor == 1r && piPower == 0 && offset == 0r),
  law pointUnprefixed() = (offset != 0r).implies(prefixes == []),
}
struct UnitSpelling { spelling: UnitName, means: UnitText }

m = UnitDef(name: "m", unit: #base, prefixes: ["f", "p", "n", "μ", "m", "c", "d", "k"]);   // a base name
K = UnitDef(name: "K", unit: #base, prefixes: ["n", "μ", "m"]);     // the kelvin, a base name
degK = UnitDef(name: "°K", ascii: "degK", unit: "K");               // an alias: °K and degK are K
rad = UnitDef(name: "rad", unit: #base, prefixes: ["n", "μ", "m"]); // the radian, a base name
J = UnitDef(name: "J", unit: "N m", prefixes: ["n", "μ", "m", "k", "M", "G", "T", "P", "E"]);   // an alias
Bq = UnitDef(name: "Bq", unit: "1/s #activity", prefixes: ["m", "k", "M", "G", "T", "P"]);     // an alias with a kind
h = UnitDef(name: "h", unit: "s", factor: 3600r);                   // a scaled name
percent = UnitDef(name: "%", unit: "#ratio", factor: 1r/100r);      // a scaled name with a kind
pc = UnitDef(name: "pc", unit: "au", factor: 648000r, piPower: -1, prefixes: ["k", "M", "G"]);
celsius = UnitDef(name: "°C", ascii: "degC", unit: "K", offset: 27315r/100r);   // a point unit
ohm = UnitDef(name: "Ω", ascii: "Ohm", unit: "V/A", prefixes: ["μ", "m", "k", "M", "G"]);
micron = UnitSpelling(spelling: "micron", means: "μm");
byte = UnitDef(name: "B", unit: #base, prefixes: ["k", "M", "G", "T", "P", "E", "Z", "Y", "Ki", "Mi", "Gi", "Ti", "Pi", "Ei"]);   // the byte, a base name
bit = UnitDef(name: "bit", unit: "B", factor: 1r/8r, prefixes: ["k", "M", "G", "T", "Ki", "Mi", "Gi", "Ti"]);
px = UnitDef(name: "px", unit: #base);                              // a program's own base name
```

<!-- DESIGN.md:1708 layer L18: ring L7, word L18 (@stack), label none; section [sec:facets] 3 -->
```zed
@stack(bytes: 1 with units("GiB")) deep(n: int) = n + 1;   // 1073741824 B
@stack(1 with units("Gbit")) wide(n: int) = n + 1;     // 125000000 B: one parameter, so no label is needed
@stack(bytes: 65536) leaf(n: int) = n + 1;             // a bare number, 65536 B
heat(t: f64 with units("K")) = t;
warm = heat(t: 20.0 with units("degC"));               // t is 293.15 K
take(n: int with assumedUnits("B")) = n;
a = take(n: 3);                                         // 3 with units("B")
b = take(n: 3 with units("bit"));                       // 1 with units("B"), rounded up
s = "naïve";                                           // NFC, as all source is (step L1.1): ï is U+00EF
long = s::len > 3;                                     // true: 5 codepoint > 3 codepoint
bytesLong = s::u8::len > 5;                            // true: 6 B > 5 B, exactly, since ï is 2 B in NFC
nfdBytes = s::nfd::u8::len;                            // 7 B: in NFD ï is i and U+0308, 1 B and 2 B
nfdLong = s::nfd::len;                                 // 6 codepoint
first = s::u8[0];                                      // 110, the key 0 read in B
small = s::u8::len < (1 with units("kB"));             // true: 6 B < 1000 B, compared in B
utf16Len = s::chars::len;                              // 5 char16: each code point here is one UTF-16 unit
// c = take(n: 3 with units("m"));                     // ✗ Argument whose unit does not convert to its parameter's: n is in B, and m does not convert to B
// d = s::len > (3 with units("B"));                   // ✗ Units that differ where an operation requires equal ones: s::len : codepoint > 3 : B
// e = s::u8::len + (1 with units("kB"));              // ✗ Units that differ where an operation requires equal ones: s::u8::len : B + 1 : kB; write s::u8::len + (1 with units("kB")).to("B")
// f = s::codepoints[s::u8::len - 1];                  // ✗ Argument whose unit does not convert to its parameter's: s::codepoints is keyed in codepoint, and s::u8::len - 1 is in B
// g = s::chars::len < (80 with units("char"));        // ✗ Unit name not declared: char; write units("char16") for UTF-16 code units or units("codepoint") for code points
```

<!-- DESIGN.md:1742 layer L12: ring L7, word L12 (units), label none; section [sec:facets] 4 -->
```zed
force = 3.0f64 with units("N");
arm = 2.0f64 with units("m");
work = force * arm;                          // 6.0 with units("J"), no kind
moment = (force * arm).to("N m #torque");    // 6.0 with units("N m #torque")
source = 4.0e3f64 with units("Bq");          // the kind #activity
doubled = 2.0 * source;                      // 8.0e3 with units("Bq"), the kind kept
share = 25r with units("%");
part = share.to("1");                        // 1/4 with units("1"), no kind
// total = work + moment;                    // ✗ Units that differ where an operation requires equal ones: work is in kg m^2/s^2 (J) and moment in kg m^2/s^2 #torque
```

<!-- DESIGN.md:1765 layer L12: ring L7, word L12 (units), label none; section [sec:facets] 5 -->
```zed
noon = 20.0f64 with units("°C");
morning = 12.5f64 with units("degC");
rise = noon - morning;                       // 7.5 with units("K")
absolute = noon.to("K");                     // 293.15 with units("K")
later = noon + (2.0 with units("K"));        // 22.0 with units("°C")
later2 = (25.0f64 with units("degC")) + (5.0 with units("K"));  // 30.0 with units("°C")
warmer = noon > morning;                     // true
// both = morning + noon;                    // ✗ No `+` of two point readings: morning and noon are readings in °C; add a difference in K
// gradient = noon / (2.0 with units("m")); // ✗ Point unit in a product, quotient or power: noon is a reading in °C; write noon.to("K")
```

<!-- DESIGN.md:1786 layer L12: ring L7, word L12 (units), label none; section [sec:facets] 6 -->
```zed
size = 3 with units("GiB");
disk = 3 with units("GB");
bigger = size > disk;                        // true: 3221225472 B > 3000000000 B, compared in B
flag = (9 with units("bit")) > (1 with units("B"));   // true: 9 bit > 8 bit, compared in bit
walk = 900.0f64 with units("m");
near = walk < (1.0 with units("km"));        // true: 900 m < 1000 m, compared in m
noon = 20.0f64 with units("°C");
hot = noon.to("K") > (290.0 with units("K"));  // true: 293.15 K > 290 K
// far = walk + (1.0 with units("km"));      // ✗ Units that differ where an operation requires equal ones: walk : m + 1.0 : km; write walk + (1.0 with units("km")).to("m")
// odd = noon > (290.0 with units("K"));     // ✗ Point reading compared with a value that is not a reading: noon : °C > 290.0 : K; write noon.to("K") > (290.0 with units("K"))
```

<!-- DESIGN.md:1810 layer L12: ring L7, word L12 (units), label none; section [sec:facets] 7 -->
```zed
len = 5.0f64 with units("m");
y = log(len);                                // 1.6094379124341003 with units("log(m)")
sq = log(len * len);                         // 3.2188758248682006 with units("log(m^2)")
twice = 2.0 * y;                             // 3.2188758248682006 with units("log(m^2)")
same = twice == sq;                          // true
back = exp(y);                               // 4.999999999999999 with units("m")
far = log10(1000.0 with units("m"));         // 3.0 with units("log10(m)")
nearKm = far.to("log10(km)");                // 0.0 with units("log10(km)")
inE = log(1.0 with units("km")).to("log(m)");  // 6.907755278982137 with units("log(m)")
ratio = y - log(1.0 with units("m"));        // 1.6094379124341003 with units("1")
// bad = y * y;                              // ✗ Logarithmic unit in an operation that would change with the unit: y is in log(m), and a product of two logarithms has no unit
// big = y > 0.0;                            // ✗ Logarithmic unit in an operation that would change with the unit: y is in log(m) and 0.0 has no unit; compare with log(1.0 with units("m"))
// wrong = exp(far);                         // ✗ Exponential whose base differs from the logarithm's: far is in log10(m); write 10.0^far
```

<!-- DESIGN.md:1840 layer L12: ring L12, word L12 (units), label none; section [sec:facets] 8 -->
```zed
n = 1200 with units("m");
x = f64(n) else round(n);                    // 1200.0 with units("m")
label = "${n}";                              // "1200 m"
column = "${n without units("m")}";          // "1200"
count = (n without units("m")) div 100;      // 12, no unit
km = (f64(n) else round(n)).to("km");        // 1.2 with units("km")
// wrongDrop = n without units("km");        // ✗ Fact removed that the value does not carry: n is in m, not km
// cleaned = userInput without taint(#user); // ✗ Fact removed from a facet that does not allow it: taint is lowered only by a named sanitizer
```

<!-- DESIGN.md:1908 layer L14: ring L10, word L14 (quat), label none; section [sec:linalg] 1 -->
```zed
matmul(positional v: (c -> T), positional b: (c -> k -> T)) = (v, b) into (k -> c >< (+) -> v[c] * b[c][k]);
matmul(positional a: (r -> c -> T), positional v: (c -> T)) = (a, v) into (r -> c >< (+) -> a[r][c] * v[c]);
dot(positional u: (i -> T), positional v: (i -> T)) = (u, v) into (i >< (+) -> conj(u[i]) * v[i]);
cross(positional u: (int[0..<3] -> T), positional v: (int[0..<3] -> T)) = (quat(0, u) * quat(0, v)).im;
cross(positional u: (int[0..<7] -> T), positional v: (int[0..<7] -> T)) = (oct(0, u) * oct(0, v)).im;
```

<!-- DESIGN.md:1920 layer L14: ring L14, word L14 (layout), label none; section [sec:linalg] 2 -->
```zed
type Rgb = [f32; 3];                                              // int[0..<3] -> f32
type Batch = [f32; n: _, h: 224, w: 224, c: 3] with layout(n, h, w, c);
scale(positional s: T, positional v: [T; n]) = s * v;            // : [T; n]
```

<!-- DESIGN.md:1932 layer L14: ring L10, word L14 (matmul), label none; section [sec:linalg] 3 -->
```zed
type State = int[0..<2];
step(positional f: ((i: State with units(["m", "m/s"])) -> (j: State with units(["1/m", "s/m"])) -> f64),
     positional x: ((j: State with units(["m", "m/s"])) -> f64)) = f.matmul(x);
// step(f, x) : (i: State with units(["m", "m/s"])) -> f64
```

<!-- DESIGN.md:1959 layer L17: ring L10, word L17 (@total), label none; section [sec:staging] 1 -->
```zed
  // ends: n falls by 1 at each call and stays at least 0; nothing is printed
  countDown(positional n: int[0..]) = if n == 0 { 0 } else { countDown(n - 1) + 1 };

  // does not end on the input 1 (1, -1, -3, ...): every build warns at `halve(n - 2)`, printing n = 1,
  // and --total rejects it
  halve(positional n: int) = if n == 0 { 0 } else { halve(n - 2) + 1 };

  // with the deadline before main, the warning at `halve(n - 2)` adds that the run ends after 10 s,
  // with exit status 3 and no value, so this program ends on every input; --total still rejects it
  @timeout(10 with units("s"))
  main(m: MainArgs) {
    k = int(m.args[0] else "") else 0;
    m.stdout <- "${countDown(5)} ${halve(k)}";
  }

  // @total: the read has a timeout, so it ends with a value, the text, #ioError or #timeout;
  // without the @timeout the build rejects the read, in every tier
  @total
  config() -> Utf8String = (@timeout(2 with units("s")) main::files["config.txt"]) else "";
```

<!-- DESIGN.md:2004 layer L11: ring L10, word L11 (Constraints), label none; section [sec:introspection] 1 -->
```zed
type Shape =
    #scalar(name: Utf8String, constraints: Constraints)  // int, rat, f64, bool, …, with its refinement: int[0..<10]
  | #string(name: Utf8String, syntax: Grammar | #none, constraints: Constraints)   // Utf8String and the other string types, by name, or one matching grammar { … }
  | #atom(name: Utf8String, payload: Type | #none)       // #red, or #ioError(op: Utf8String, path: Utf8String, why: Utf8String)
  | #struct(name: Utf8String | #none, fields: [Field], syntax: Grammar | #none)
  | #interface(name: Utf8String, fields: [Field])
  | #tuple(items: [Type])
  | #union(name: Utf8String | #none, members: [Type])
  | #morphism(guarantee: Type, permission: Type, value: Type) // K -> V when guarantee == permission; K ->? V when the guarantee is empty; L .. U -> V otherwise
  | #function(params: [Param], result: Type)
  | #refined(base: Type, predicate: Ast)             // t where p, an opaque refinement (sec:domains)
  | #negation(of: Type)
  | #intersection(parts: [Type]);
struct Field { key: _, name: Utf8String, valueType: Type, default: Ast | #none, facets: [Ast] }
struct Param { name: Utf8String | #none, kind: #positional | #named, valueType: Type, default: Ast | #none }
```

<!-- DESIGN.md:2046 layer L11: ring L3, word L11 (::shape), label none; section [sec:introspection] 2 -->
```zed
encode(positional v: T) -> Utf8String = match T::shape {
  #struct(fields:) -> "{" ++ (fields.map(f -> quote(f.name) ++ ": " ++ encode(v[f.key])) >< ((a, b) -> a ++ ", " ++ b) else "") ++ "}",
  #string          -> quote(v),
  #atom(name:, payload: #none) -> quote(name),
  _                -> Utf8String(v),
};
// For u: User, encode(u) specializes to "{\"id\": " ++ Utf8String(u.id) ++ ", \"name\": " ++ quote(u.name) ++ "}":
// the match, the map over the two fields, and the fold all run at build.
```

<!-- DESIGN.md:2067 layer L22: ring L3, word L22 (expand), label none; section [sec:symbolic] 1 -->
```zed
p = ((x: rat) -> (x + 1r)^2)::source;
e = expand(p);         // the tree of (x: rat) -> x^2 + 2r * x + 1r
d = derivative(p);     // the tree of (x: rat) -> 2r * x + 2r
```

<!-- DESIGN.md:2088 layer L15: ring L15, word L5 (sort), label none; section [sec:verification] 1 -->
```zed
law addComm(a: int, b: int) = a + b == b + a;
law sortIdempotent(xs: [int]) = xs.sort(asc x -> x).sort(asc x -> x) == xs.sort(asc x -> x);
law noOverdraft(s: Account, t: Txn where t.amount > 0) = (apply(s, t) else s).balance >= 0;   // `else` strips the loose #rejected: the body is exactly bool
```

<!-- DESIGN.md:2123 layer L6: ring L3, word L6 (Ast), label none; section [sec:verification] 2 -->
```zed
type Proof = #eval                                            // discharge by enumeration (rung 1)
           | #domain                                          // by the store's lattices and Presburger layer (rung 2)
           | #rewrite(rule: LawId, at: Path, bindings: Bindings) // one equational step
           | #chain(steps: [Proof], claims: [Ast])            // each step proves its claim
           | #cases(on: Ast, arms: Member -> Proof)           // one arm per union member, or `true` and `false`
           | #induction(on: Binder, base: Proof, step: Proof) // `ih` bound in `step`
           | #use(rule: LawId, args: [Ast])                   // instantiate a proved law
           | #implies(assume: Ast, then: Proof)               // discharge under a hypothesis
           | #reflect(sound: LawId)                           // run a decision procedure proved sound (sec:checking_in_zed)
           | #assume(why: Utf8String);                            // rung 9, recorded at the site
```

<!-- DESIGN.md:2161 layer L1: ring L1, word L1 (MainArgs), label none; section [sec:checking_in_zed] 1 -->
```zed
// rejected: `b ^ (2^64)` needs at least 128 EiB, and Linux x86_64 addresses 16 EiB
main(m: MainArgs) {
  b = 2^64 + 13;
  m.stdout <- String(b ^ (2^64));
}

// also rejected, though the branch runs only when the first argument is more than 5
main(m: MainArgs) {
  k = int(m.args[0] else "") else 0;
  m.stdout <- if k > 5 { String((2^64 + 13) ^ (2^64)) } else { "few" };
}

// accepted: the size depends on `k`, which the input gives. With the argument 40 the power
// asks for 128 GiB; on a machine that cannot give it the run stops at `2r^(2^k)` with
// "Number too large for memory" on standard error and exit status 3, unless `main` declares a memory limit (sec:ports)
grow(k: int) {
  return if k >= 0 { 2r^(2^k) } else { 0r };
}
main(m: MainArgs) {
  k = int(m.args[0] else "") else 0;
  m.stdout <- String(grow(k: k)) else "";
}
```

<!-- DESIGN.md:2239 layer L12: ring L12, word L6 (Store), label none; section [sec:checking_in_zed] 2 -->
```zed
struct Lattice(positional E) {
  le:     (E, E) -> bool,                               // the order: le(a, b) when a is below b
  join:   (E, E) -> E,
  top:    E,
  meet:   ((E, E) -> E | #empty) | #none,               // #empty when no value lies below both; #none for a lattice with no meet, such as cost's
  widen:  (E, E) -> E = join,                           // a lattice of finite height widens by its join
  narrow: (E, E) -> E = (a, b) -> b,
  law reflexive(a: E) = le(a, a),
  law antisymmetric(a: E, b: E) = (le(a, b) && le(b, a)).implies(a == b),
  law transitive(a: E, b: E, c: E) = (le(a, b) && le(b, c)).implies(le(a, c)),
  law topAbove(a: E) = le(a, top),
  law joinAbove(a: E, b: E) = le(a, join(a, b)) && le(b, join(a, b)),
  law joinLeast(a: E, b: E, c: E) = (le(a, c) && le(b, c)).implies(le(join(a, b), c)),
  law meetGreatest(a: E, b: E, c: E) = match meet {
    #none -> true,
    m     -> match m(a, b) {
      #empty -> !(le(c, a) && le(c, b)),
      d      -> le(d, a) && le(d, b) && (le(c, a) && le(c, b)).implies(le(c, d)),
    },
  },
  law widenAbove(a: E, b: E) = le(a, widen(a, b)) && le(b, widen(a, b)),
  law narrowBetween(a: E, b: E) = le(b, a).implies(le(b, narrow(a, b)) && le(narrow(a, b), a)),
}

struct Facet(positional E, positional V) {
  kind:        #semantic | #evidence | #hint,
  lattice:     Lattice(E),                              // finite, or a prelude lattice such as flat(…) (step M0.5)
  holds:       ((E, V) -> bool) | #none where (holds is #none) == (kind != #evidence) = #none,   // required for an evidence facet, absent otherwise
  transfer:    (_, (E,) | (E, E)) -> E,                 // the operator atom (#add, #neg, …, family fixed at step S.3) and its operands' elements
  abstract:    ((Ast, Ast, (Ast) -> E) -> E) | #none = #none,
  project:     (_, (E, E) | (E, E, E), int[0..=2]) -> E = (op, es, i) -> match es {   // the operands' elements, then the result's
                 (a, _)    -> if i == 1 { transfer(op, (a,)) } else { lattice.top },
                 (a, b, _) -> if i == 2 { transfer(op, (a, b)) } else { lattice.top },
               },
  shares:      (E) -> #constant(V) | #none = e -> #none,
  show:        ((E, Ast) -> Ast) | #none = #none,       // #none: holds(e, x) for an evidence facet, x with name(e) for a semantic one
  reject:      ((E, E, Ast) -> Rejection(_)) | #none = #none,   // #none: a rejection at the site whose witnesses are the two elements written by show
  printedForm: #annotation | #with = #with,             // (sec:facets)
  typeChange:  (Type) -> Type = t -> t,                 // (sec:facets)
  removable:   bool = false,                            // whether `x without name(args)` may drop a fact (sec:facets)
  law transferMono1(op: _, a: E, c: E) = lattice.le(a, c).implies(lattice.le(transfer(op, (a,)), transfer(op, (c,)))),
  law transferMono2(op: _, a: E, b: E, c: E, d: E) =
    (lattice.le(a, c) && lattice.le(b, d)).implies(lattice.le(transfer(op, (a, b)), transfer(op, (c, d)))),
  law projectMono1(op: _, a: E, r: E, c: E, s: E, i: int[0..=1]) =
    (lattice.le(a, c) && lattice.le(r, s)).implies(lattice.le(project(op, (a, r), i), project(op, (c, s), i))),
  law projectMono2(op: _, a: E, b: E, r: E, c: E, d: E, s: E, i: int[0..=2]) =
    (lattice.le(a, c) && lattice.le(b, d) && lattice.le(r, s)).implies(lattice.le(project(op, (a, b, r), i), project(op, (c, d, s), i))),
  law topSound(x: V) = match holds { #none -> true, h -> h(lattice.top, x) },
  law transferSound1(op: _, a: E, x: V) = match holds { #none -> true, h -> h(a, x).implies(h(transfer(op, (a,)), op(x))) },
  law transferSound2(op: _, a: E, b: E, x: V, y: V) = match holds {
    #none -> true,
    h     -> (h(a, x) && h(b, y)).implies(h(transfer(op, (a, b)), op(x, y))),
  },
  law projectSound1(op: _, a: E, r: E, x: V) = match holds {
    #none -> true,
    h     -> (h(a, x) && h(r, op(x))).implies(h(project(op, (a, r), 0), x) && h(project(op, (a, r), 1), op(x))),
  },
  law projectSound2(op: _, a: E, b: E, r: E, x: V, y: V) = match holds {
    #none -> true,
    h     -> (h(a, x) && h(b, y) && h(r, op(x, y))).implies(
               h(project(op, (a, b, r), 0), x) && h(project(op, (a, b, r), 1), y) && h(project(op, (a, b, r), 2), op(x, y))),
  },
  law meetSound(a: E, b: E, x: V) = match (holds, lattice.meet) {
    (#none, _) -> true,
    (_, #none) -> true,
    (h, m)     -> (h(a, x) && h(b, x)).implies(match m(a, b) { #empty -> false, c -> h(c, x) }),
  },
  law sharesSound(e: E, x: V) = match (holds, shares(e)) {
    (#none, _)        -> true,
    (_, #none)        -> true,
    (h, #constant(c)) -> h(e, x).implies(x == c),
  },
}

struct Reduction(positional E) {                        // (sec:constraints)
  of:     Facet(E, _),
  reads:  [Facet(_, _)],
  reduce: (E, Store) -> E,
  law reduceMono(e: E, e2: E, s: Store, s2: Store) =
    (of.lattice.le(e, e2) && reads.all(f -> f.lattice.le(s.of(f), s2.of(f)))).implies(of.lattice.le(reduce(e, s), reduce(e2, s2))),
  law reduceSound(e: E, s: Store, x: _) = match of.holds {
    #none -> true,
    h     -> (h(e, x) && reads.all(f -> match f.holds { #none -> true, g -> g(s.of(f), x) })).implies(h(reduce(e, s), x)),
  },
}

struct Rejection(positional W) {                        // (sec:diagnostics)
  site:    Ast,                                         // the expression the rejection names
  witness: W,                                           // the value or element that shows the failure
  menu:    [Ast],                                       // the repairs, each the program's own code rewritten
}
```

<!-- DESIGN.md:2335 layer L12: ring L10, word L12 (parity), label none; section [sec:checking_in_zed] 3 -->
```zed
type Parity = #even | #odd | #either;
parity: Facet(Parity, int) = Facet(
  kind:     #evidence,
  lattice:  flat([#even, #odd], top: #either),     // a prelude lattice over Parity's atoms; finite, so the monotonicity laws are enumerated
  holds:    (p, x) -> match p { #even -> x mod 2 == 0, #odd -> x mod 2 == 1, #either -> true },
  transfer: (op, es) -> match (op, es) {
    (#neg, (a,))   -> a,
    (#add, (a, b)) -> if a == #either || b == #either { #either } else if a == b { #even } else { #odd },
    (#mul, (a, b)) -> if a == #even || b == #even { #even } else if a == #odd && b == #odd { #odd } else { #either },
    _              -> #either,
  },
);

half(positional x: int with parity(#even)) = x div 2;                     // a demand on the argument's fact
g(n: int with parity(#odd)) = half(n + n);                              // ✓ transferSound2 at #add splits by cases (rung 5) into Presburger facts (rung 2): Proved, so the demand is met
h(n: int with parity(#odd), m: int with parity(#even)) = half(n * m);   // ✓ transferSound2 at #mul is proved by the residue identity of int (sec:property_tracking) and the split over the listed atoms (rung 5): Proved, so the demand is met with no test
seven = 7 with parity(#odd);                                            // attaching a fact to a value is an obligation: holds(#odd, 7), rung 1
```

<!-- DESIGN.md:2391 layer L22: ring L22, word none, label none; section [sec:theories] 1 -->
```zed
interface Semigroup(positional T) {
  mul: (T, T) -> T,
  law mulAssoc(a: T, b: T, c: T) = mul(mul(a, b), c) == mul(a, mul(b, c)),
}

interface Monoid(positional T) {
  import Semigroup(T),
  one: T,
  law oneMul(a: T) = mul(one, a) == a,
  law mulOne(a: T) = mul(a, one) == a,
}

interface NonCommRing(positional T) {
  import Monoid(T),
  add: (T, T) -> T,
  zero: T,
  neg: (T) -> T,
  law addAssoc(a: T, b: T, c: T) = add(add(a, b), c) == add(a, add(b, c)),
  law addComm(a: T, b: T) = add(a, b) == add(b, a),
  law addZero(a: T) = add(a, zero) == a,
  law addNeg(a: T) = add(a, neg(a)) == zero,
  law distrib(a: T, b: T, c: T) = mul(a, add(b, c)) == add(mul(a, b), mul(a, c)),
  law distribRight(a: T, b: T, c: T) = mul(add(a, b), c) == add(mul(a, c), mul(b, c)),
}

interface CommRing(positional T) {
  import NonCommRing(T),
  law mulComm(a: T, b: T) = mul(a, b) == mul(b, a),
}

intRing: CommRing(int) = { mul: (*), one: 1, add: (+), zero: 0, neg: (a -> -a) };
```

<!-- DESIGN.md:2433 layer L22: ring L22, word L22 (CommRing), label none; section [sec:theories] 2 -->
```zed
law square(R: CommRing(T), a: T, b: T) = (a + b) * (a + b) == a * a + 2 * a * b + b * b
proof {
  (a + b) * (a + b)
    == (a + b) * a + (a + b) * b
    == a * a + b * a + (a * b + b * b)
    == a * a + 2 * a * b + b * b
}
```

<!-- DESIGN.md:2447 layer L22: ring L15, word L22 (Monoid), label none; section [sec:theories] 3 -->
```zed
pow(M: Monoid(T), x: T, n: int[0..]) -> T = if n == 0 { 1 } else { pow(M:, x:, n: n - 1) * x };

law powAdd(M: Monoid(T), x: T, m: int[0..], n: int[0..]) =
  pow(M:, x:, n: m + n) == pow(M:, x:, n: m) * pow(M:, x:, n: n)
proof { byInduction(n) }                        // base by mulOne; step by ih and mulAssoc at rung 3
```

<!-- DESIGN.md:2457 layer L22: ring L2, word L22 (Monoid), label none; section [sec:theories] 4 -->
```zed
additive(R: CommRing(T)) -> Monoid(T) = { mul: R.add, one: R.zero };   // mulAssoc is R.addAssoc; mulOne is R.addZero; oneMul by addComm
```

<!-- DESIGN.md:2536 layer L22: ring L22, word none, label none; section [sec:theories] 5 -->
```zed
interface MonoInt {
  f: (int) -> int,
  law mono(a: int, b: int) = (a <= b).implies(f(a) <= f(b)),
}

law monoTwice(M: MonoInt, a: int, b: int) = (a <= b).implies(M.f(M.f(a)) <= M.f(M.f(b))) proof {
  #implies(assume: a <= b, then: #chain(steps: [
    #use(rule: M.mono, args: [a, b]),
    #use(rule: M.mono, args: [M.f(a), M.f(b)]),
  ], claims: [M.f(a) <= M.f(b), M.f(M.f(a)) <= M.f(M.f(b))]))
}
```

<!-- DESIGN.md:2950 layer L3: ring L3, word L3 (map), label none; section [sec:corner_cases] 1 -->
```zed
total(positional xs: [int]) -> int {
  s = xs.sum;
  t = xs.map(x -> x * 2).sum;
  return s + t;
  // in place of the line above:
  // return s;                   // ✗ Block binding that nothing reads: t is bound and never read, so xs.map(x -> x * 2).sum is never computed
}
```

<!-- DESIGN.md:3023 layer L1: ring L1, word L1 (Utf8String), label none; section [sec:memory] 1 -->
```zed
  // the width of the header, and the text twice
  page(name: Utf8String, text: Utf8String) -> (int, Utf8String) {
    header = "Report for " ++ name;   // made first
    body = text ++ "\n" ++ text;      // made later, on a branch that does not read `header`
    width = header.len;               // the last use of `header`: it is released here
    (width, body)                     // `body` goes to the caller, which releases it after its own last use
  }
```

<!-- DESIGN.md:3099 layer L21: ring L7, word L21 (peers), label none; section [sec:robustness] 1 -->
```zed
prices: Utf8String ->? rat with peers(["a", "b"], assign: #roundRobin);

main(m: MainArgs) {
  m.stdout <- m.stdin.map(sku -> "${prices[sku] else 0r}");
}
```

<!-- DESIGN.md:3118 layer L7: ring L7, word L7 (u8), label none; section [sec:ffi] 1 -->
```zed
@foreign struct SockAddr { family: int with bits(16), data: [u8] with length(14) }
@foreign struct AddrInfo {
  flags: i32, family: i32, socktype: i32, protocol: i32,
  addrlen: int with bits(32),
  addr: Ptr(SockAddr) | #none,
  canonname: Ptr([u8] with terminated(0)) | #none,
  next: Ptr(AddrInfo) | #none,
}
@foreign("c", "freeaddrinfo") @nonblocking freeAddrInfo: (res: Ptr(AddrInfo)) -> #ok;
@foreign("c", "getaddrinfo") @blocking getAddrInfo: (node: [u8] with terminated(0), service: [u8] with terminated(0), hints: Ptr(AddrInfo) | #none) -> (i32, Ptr(AddrInfo) | #none with release(freeAddrInfo));
```

<!-- DESIGN.md:3133 layer L7: ring L7, word L7 (i32), label none; section [sec:ffi] 2 -->
```zed
  @foreign("counter", "counter_next") @blocking next: () -> i32;

  f(y: bool) -> i32 | #none {
    x = next() else 0;
    return if y { x } else { #none };
  }
```

<!-- DESIGN.md:3151 layer L7: ring L7, word L7 (u64), label none; section [sec:ffi] 3 -->
```zed
  @foreign struct Device {}
  @foreign struct Buffer {}
  @foreign struct Extension {}
  @foreign struct AllocationCallbacks {}
  @foreign struct BufferCreateInfo {
    structType: i32, next: Ptr(Extension) | #none, flags: u32, size: u64, usage: u32,
    sharingMode: i32, queueFamilyCount: u32, queueFamilies: Ptr([u32] with length(queueFamilyCount)) | #none,
  }
  @foreign("vulkan", "vkDestroyBuffer") @nonblocking destroyBuffer: (device: Ptr(Device), buffer: Ptr(Buffer), allocator: Ptr(AllocationCallbacks) | #none) -> #ok;
  @foreign("vulkan", "vkCreateBuffer") @blocking createBuffer: (device: Ptr(Device), info: Ptr(BufferCreateInfo), allocator: Ptr(AllocationCallbacks) | #none) -> (i32, Ptr(Buffer) | #none with release(destroyBuffer, device, allocator));
```

<!-- DESIGN.md:3167 layer L7: ring L7, word L7 (u32), label none; section [sec:ffi] 4 -->
```zed
  @foreign struct Env {}
  @foreign struct Txn {}
  @foreign("lmdb", "mdb_txn_abort") @nonblocking abort: (txn: Ptr(Txn)) -> #ok;
  @foreign("lmdb", "mdb_txn_begin") @blocking begin: (env: Ptr(Env), parent: Ptr(Txn) | #none, flags: u32) -> (i32, Ptr(Txn) | #none with release(abort));
  @foreign("lmdb", "mdb_txn_commit") @blocking commit: (txn: Ptr(Txn) with consumes()) -> i32;
```

<!-- DESIGN.md:3178 layer L7: ring L7, word L7 (u8), label none; section [sec:ffi] 5 -->
```zed
  @foreign struct Zip {}
  @foreign struct Source {}
  @foreign("zip", "zip_source_free") @nonblocking sourceFree: (source: Ptr(Source)) -> #ok;
  @foreign("zip", "zip_source_file") @blocking sourceFile: (archive: Ptr(Zip), path: [u8] with terminated(0), start: u64, length: i64) -> Ptr(Source) | #none with release(sourceFree);
  @foreign("zip", "zip_file_add") @blocking fileAdd: (archive: Ptr(Zip), name: [u8] with terminated(0), source: Ptr(Source) with consumes(unless: -1), flags: u32) -> i64;
```

<!-- DESIGN.md:3188 layer L2: ring L2, word none, label none, documentation notation; section [sec:ffi] 6 -->
```zed
  match sourceFile(archive:, path:, start: 0, length: -1) {
    #none -> -1,
    source -> match fileAdd(archive:, name:, source:, flags: 0) {
      -1 -> fileAdd(archive:, name: spare, source:, flags: 0),
      index -> index,
    },
  }
```

<!-- DESIGN.md:3210 layer L7: ring L7, word L7 (u8), label none; section [sec:ffi] 7 -->
```zed
  @foreign struct File {}
  @foreign("c", "fclose") @blocking fclose: (file: Ptr(File) with consumes()) -> i32;
  @foreign("c", "fputs") @blocking fputs: (s: [u8] with terminated(0), file: Ptr(File)) -> i32;
  @foreign("c", "fopen") @blocking fopen: (path: [u8] with terminated(0), mode: [u8] with terminated(0)) -> Ptr(File) | #none with release(fclose);
  @foreign("c", "fopen") @blocking openLog: (path: [u8] with terminated(0), mode: [u8] with terminated(0)) -> Ptr(File) | #none with release(file -> { _ = fclose(file) else #ok; #ok });
```

<!-- DESIGN.md:3222 layer L7: ring L7, word L7 (u8), label none; section [sec:ffi] 8 -->
```zed
  @foreign struct Lock {}
  @foreign("locks", "lock_release") @nonblocking unlock: (lock: Ptr(Lock)) -> #ok;
  @foreign("locks", "lock_acquire") @blocking acquire: (path: [u8] with terminated(0)) -> Ptr(Lock) with release(unlock);
```

<!-- DESIGN.md:3241 layer L7: ring L7, word L7 (u8), label none; section [sec:ffi] 9 -->
```zed
  @foreign struct Db {}
  @foreign struct Stmt {}
  @foreign("sqlite3", "sqlite3_close_v2") @blocking close: (db: Ptr(Db) with consumes()) -> i32;
  @foreign("sqlite3", "sqlite3_finalize") @nonblocking finalize: (stmt: Ptr(Stmt) with consumes()) -> i32;
  // the releases Zed makes drop the codes: close_v2 frees the handle whatever it returns,
  // and finalize repeats the error of the statement's last step, which the program has seen
  @foreign("sqlite3", "sqlite3_open") @blocking open: (path: [u8] with terminated(0)) -> (i32, Ptr(Db) | #none with release(db -> { _ = close(db) else #ok; #ok }));
  @foreign("sqlite3", "sqlite3_prepare_v2") @blocking prepare: (db: Ptr(Db), sql: [u8] with terminated(0), bytes: i32, tail: Ptr(Ptr([u8] with terminated(0))) | #none) -> (i32, Ptr(Stmt) | #none with arg(3) with release(stmt -> { _ = finalize(stmt) else #ok; #ok }) with keeps(db));

  // the database and a statement on it, or the code of the call that failed
  openQuery(path: Utf8String, sql: Utf8String) -> (Ptr(Db), Ptr(Stmt)) | i32 {
    rc, opened = open(path:);
    match opened {
      #none -> rc,
      db -> if rc != 0 { rc } else {   // sqlite3_open can give a handle and an error: Zed closes it
        rc2, prepared = prepare(db:, sql:, bytes: -1, tail: #none);
        match prepared {
          #none -> rc2,         // prepare was the last use of db on this path: Zed closes it
          stmt -> (db, stmt),   // both returned; the caller's releases finalize stmt, then close db
        }
      },
    }
  }
```

<!-- DESIGN.md:3279 layer L7: ring L7, word L7 (u8), label none; section [sec:ffi] 10 -->
```zed
  @foreign struct Termios {
    iflag: u32, oflag: u32, cflag: u32, lflag: u32,
    line: u8, cc: [u8] with length(32),
    ispeed: u32, ospeed: u32,
  }
  @foreign("c", "tcgetattr") @blocking tcgetattr: (fd: i32) -> (i32, Termios with arg(1));
  @foreign("c", "tcsetattr") @blocking tcsetattr: (fd: i32, when: i32, mode: Ptr(Termios)) -> i32;
  // getchar is MT-Safe (fgetc(3)), so it may run on a thread of its own: waiting for a key leaves the C library's thread free
  @thread(#keys) @foreign("c", "getchar") @blocking getKey: (raw: Termios with notPassed(duringStop: #release)) -> i32 with anyThread();

  // glibc's cfmakeraw: no echo, no line editing, no signals from keys, 8-bit bytes, a read waits for one byte
  makeRaw(t: Termios) -> Termios {
    t with {
      iflag = t.iflag.bitAnd(bitNot(1515, width: 32)),            // IGNBRK BRKINT PARMRK ISTRIP INLCR IGNCR ICRNL IXON
      oflag = t.oflag.bitAnd(bitNot(1, width: 32)),               // OPOST
      lflag = t.lflag.bitAnd(bitNot(32843, width: 32)),           // ECHO ECHONL ICANON ISIG IEXTEN
      cflag = t.cflag.bitAnd(bitNot(304, width: 32)).bitOr(48),   // CSIZE and PARENB off, CS8 on
      cc[6] = 1, cc[5] = 0,                                       // VMIN 1, VTIME 0
    }
  }

  // puts the saved mode back; 2 is TCSAFLUSH
  leaveRaw(fd: i32, saved: Termios) -> #ok {
    _ = tcsetattr(fd:, when: 2, mode: saved) else #ok;
    #ok
  }

  // the saved mode is the token: while it is in use, the terminal is raw
  enterRaw(fd: i32) -> (i32, Termios | #none with release(leaveRaw, fd)) {
    rc, saved = tcgetattr(fd:);
    return if rc != 0 { (rc, #none) } else {
      rc2 = tcsetattr(fd:, when: 2, mode: makeRaw(saved)) else -1;
      if rc2 != 0 { (rc2, #none) } else { (0, saved) }
    };
  }

  main(m: MainArgs) -> int {
    _, mode = enterRaw(fd: 0);
    return match mode {
      #none -> 1,
      raw -> {
        k = getKey(raw:);   // the last use of raw: Zed calls leaveRaw(fd: 0, saved: raw) when getchar returns
        if k == 113 { 0 } else { 2 }
      },
    };
  }
```

<!-- DESIGN.md:3332 layer L7: ring L7, word L7 (u8), label none; section [sec:ffi] 11 -->
```zed
  struct Dir { fd: i32 }
  @foreign("c", "open") @blocking openPath: (path: [u8] with terminated(0), flags: i32) -> i32;
  @foreign("c", "chdir") @blocking chdir: (path: [u8] with terminated(0)) -> i32;
  @foreign("c", "fchdir") @blocking fchdir: (fd: i32) -> i32;
  @foreign("c", "close") @blocking closeFd: (fd: i32) -> i32;
  // a path relative to the directory the token holds current
  @foreign("c", "open") @blocking openIn: (dir: Dir with notPassed(), path: [u8] with terminated(0), flags: i32) -> i32;

  // goes back to the directory that was current, then closes its descriptor
  leaveDir(old: Dir) -> #ok {
    r = fchdir(fd: old.fd);
    @after(r) _ = closeFd(fd: old.fd);
    #ok
  }

  // 65536 is O_DIRECTORY on Linux, with O_RDONLY, which is 0
  enterDir(path: [u8] with terminated(0)) -> (i32, Dir | #none with release(leaveDir)) {
    old = openPath(path: ".", flags: 65536);
    return if old < 0 { (old, #none) } else {
      @after(old) rc = chdir(path:);
      if rc != 0 {
        @after(rc) _ = closeFd(fd: old);
        (rc, #none)
      } else { (0, Dir(fd: old)) }
    };
  }
```

<!-- DESIGN.md:3364 layer L7: ring L7, word L7 (release), label none; section [sec:ffi] 12 -->
```zed
  @foreign struct Curl {}
  struct CurlState {}
  @foreign("curl", "curl_global_init") @blocking globalInit: (flags: i64) -> i32;
  @foreign("curl", "curl_global_cleanup") @blocking globalCleanup: () -> #ok;
  @foreign("curl", "curl_easy_cleanup") @blocking easyCleanup: (handle: Ptr(Curl)) -> #ok;
  @foreign("curl", "curl_easy_init") @blocking easyInit: (state: CurlState with notPassed()) -> Ptr(Curl) | #none with release(easyCleanup) with keeps(state);

  // 3 is CURL_GLOBAL_ALL
  startCurl() -> CurlState | #none with release(globalCleanup) {
    return if globalInit(flags: 3) != 0 { #none } else { CurlState() };
  }
```

<!-- DESIGN.md:3383 layer L7: ring L7, word L7 (u8), label none; section [sec:ffi] 13 -->
```zed
  @foreign struct File {}
  @foreign("c", "fclose") @blocking fclose: (file: Ptr(File) with consumes()) -> i32;
  @foreign("c", "fopen") @blocking fopen: (path: [u8] with terminated(0), mode: [u8] with terminated(0)) -> Ptr(File) | #none with release(file -> { _ = fclose(file) else #ok; #ok });
  // the stream keeps buf until fclose: Zed frees buf after the stream's release
  @foreign("c", "setvbuf") @blocking setvbuf: (file: Ptr(File), buf: [u8] with length(65536) with held(by: file), mode: i32, size: u64) -> i32;

  // io_uring through a small C library over liburing, whose calls are inline functions
  @foreign struct Ring {}
  @foreign struct Page { bytes: [u8] with length(4096) }
  @foreign("uringshim", "ring_exit") @blocking ringExit: (ring: Ptr(Ring) with consumes()) -> #ok;
  @foreign("uringshim", "ring_cancel_all") @blocking cancelAll: (ring: Ptr(Ring)) -> i32;
  @foreign("uringshim", "ring_init") @blocking ringInit: (entries: u32) -> Ptr(Ring) | #none with release(ring -> { n = cancelAll(ring) else 0; @after(n) _ = ringExit(ring) else #ok; #ok });
  @foreign("uringshim", "submit_read") @blocking submitRead: (ring: Ptr(Ring), fd: i32, offset: u64, page: Ptr(Page) with held(by: ring, aligned: 4096)) -> i32;
  @foreign("uringshim", "wait_read") @blocking waitRead: (ring: Ptr(Ring)) -> (i32, Ptr(Page) | #none with arg(1) with handedBack());
  // unregister_pages cancels the pending reads and waits for them, on every return, before it calls io_uring_unregister_buffers
  @foreign("uringshim", "unregister_pages") @blocking unregisterPages: (ring: Ptr(Ring) with dropsHeld()) -> i32;
```

<!-- DESIGN.md:3406 layer L7: ring L7, word L7 (u32), label none; section [sec:ffi] 14 -->
```zed
  struct Glfw {}
  @thread(#main) @foreign("glfw", "glfwInit") @blocking glfwInit: () -> i32;
  @thread(#main) @foreign("glfw", "glfwTerminate") @blocking terminate: () -> #ok;
  @thread(#main) @foreign("glfw", "glfwPollEvents") @blocking pollEvents: (glfw: Glfw with notPassed()) -> #ok;
  @foreign struct Window {}
  @thread(#render) @foreign("glfw", "glfwMakeContextCurrent") @blocking makeCurrent: (glfw: Glfw with notPassed(), window: Ptr(Window)) -> #ok with anyThread();
  @thread(#render) @foreign("GL", "glClear") @nonblocking clear: (glfw: Glfw with notPassed(), mask: u32) -> #ok;
  @thread(#render) drawFrame(glfw: Glfw, current: #ok) -> #ok {
    @after(current) r = clear(glfw:, mask: 16384) else #ok;
    r
  }

  // 1 is GLFW_TRUE
  startGlfw() -> Glfw | #none with release(terminate) {
    return if glfwInit() != 1 { #none } else { Glfw() };
  }
```

<!-- DESIGN.md:5166 layer L10: ring L10, word L1 (Utf8String), label none; section [sec:tour_basics] 1 -->
```zed
// bindings — immutable, inferred; domains where they carry intent
x = 42;
port: int[1..=65535] = 8080;
name = "Zed";
color = #green;                         // atom; family inferred from use

// functions: equation form (terminated), block form (ended by its brace), defaults,
//   positional parameters, named arguments, currying, UFCS
//   (uniform function call syntax: x.f(a) passes x as f's first parameter — the . row of sec:lexical)
double(positional x) = x * 2;
limit(positional v, positional lo, positional hi) {
  if v < lo { lo } else if v > hi { hi } else { v }   // the export: no `;`
}
greet(positional name: Utf8String, punct = "!") = "Hi, " ++ name ++ punct;
y = 5.double.limit(0, 8);               // ≡ limit(double(5), 0, 8);  y == 8
ann = greet("Ann", punct: "?");         // positional arguments first, then named
hiAnn = greet("Ann", ...);              // currying leaves out named parameters: called hiAnn(punct: "?") or hiAnn()

// structs, unions, matching, narrowing
struct Point  { x: f64, y: f64 }
struct Circle { c: Point, r: f64 = 1 }    // a field default
struct Rect   { lo: Point, hi: Point }
type Shape = Circle | Rect;             // a union, not a hierarchy

area(s: Shape) = match s {               // arms are display entries — commas, not `;`
  Circle(r:)      -> pi * r * r,
  Rect(lo:, hi:)  -> (hi.x - lo.x) * (hi.y - lo.y),
};                                       // exhaustive, or it doesn't compile

p  = Point(x: 1, y: 2);
p2 = p with { x = 3 };                 // functional update — a new value
unit = Circle(c: p);                    // r takes its default
onAxis = Point(x: 0, ...);             // a struct is its constructor, curried by name: called onAxis(y: 1)

struct Round { import Rect, r: f64 }     // composition-import, not inheritance
```

<!-- DESIGN.md:5206 layer L6: ring L6, word none, label none; section [sec:tour_methods] 1 -->
```zed
struct Counter { n: int, hi: int }

Counter.tick() {                 // no declared return ⇒ the next receiver is the whole result
  n'  = n + 1;                   // primes build the next version of the receiver;
  hi' = max(hi, n + 1);          //   unassigned fields carry forward
}
Counter.bump(positional by) -> int {  // declared -> int, and primed, so the result is (Counter, int)
  n'  = n + by;
  hi' = max(hi, n + by);
  return n;                      // the old count rides beside the mutated receiver
}
Counter.atHi = n == hi;          // no primes, no prefix — an ordinary read

p       = Counter(n: 0, hi: 9);  // `.` is pure, so every spelling below is pure
p2      = p.tick().tick();       //   T -> T chains by composition
p3, was = p.bump(2);             //   two results, two targets — the non-OO spelling
p4, w2  = bump(p, 2);            //   ≡ the same call, written without UFCS
// p*.bump(3);                   // ✗ `*.` call on a receiver that is not a state variable: p is a value binding — no next generation to write

run = loop {
  initial c = Counter(n: 0, hi: 9); // state receiver: updated every step, boundary at t = -1
  prev = c*.bump(3);                // `*.` calls and mutates: writes c', yields the return
  until prev > 20;                  //   — one write of c' per step, as always

  // each variant below replaces the `prev = …` line; none may join it (one writer of c')
  // a, b = c*.bump(1).bump(2);     // a chain threads the receiver: ONE write of c' at the
                                    //   end, its value the links' returns, in order
  // c*.tick().tick();              // no returns ⇒ a statement, still exactly one write
  // _ = c*.bump(1); _ = c*.bump(2); // ✗ Collision: two chains, two writers of c'
  // c.bump(3);                     // ✗ An `initial` statement for a name the loop does not update: `.` never mutates, so no statement updates c
  // c', prev = c.bump(3);          // the explicit spelling; `*.` abbreviates it, both legal
};
```

<!-- DESIGN.md:5250 layer L5: ring L5, word L5 (sort), label none; section [sec:tour_collections] 1 -->
```zed
xs   = [3, 1, 4, 1, 5];                 // [int]  ≡  int[0..<5] -> int
m    = { "a" -> 1, "b" -> 2 };          // display: commas inside, `;` ends the statement;
                                        //   inferred exact {"a","b"} -> int  <:  Utf8String ->? int
tags = { #red, #green };                // set ≡ self-map
word = "never" ++ "the" ++ "less";      // Utf8String: rank-keyed, ++ concatenates by offset — O(1), rope-backed

tens = xs.map(x -> x * 10);             // same keys, new values
big  = xs.where(x -> x > 2);            // sparse subdomain (type records sparsity)
srt  = xs.sort(desc x -> x);            // [5, 4, 3, 1, 1]: a ranked source sorts flat; stability is a theorem
tot  = xs.sum;                          // = xs >< (+): sum, count, and reduce(op) are the fold in the method register

// WORD COUNT — method register:
counts = text.split(" ").group(w -> w.lower).count;
// counts : Utf8String ->? int     (f() ≡ f — a unit morphism reads as its value)
```

<!-- DESIGN.md:5267 layer L8: ring L8, word L3 (split), label none; section [sec:tour_collections] 2 -->
```zed
// the same program, symbolic register (what the optimizer reasons over):
counts = text.split(" ") as (i -> w) into (w.lower -> i -> 1) >< (+);
```

<!-- DESIGN.md:5272 layer L4: ring L1, word L4 (rekey), label none; section [sec:tour_collections] 3 -->
```zed
// group vs rekey — the grouping decision is always a visible word:
byId = users.rekey(u -> u.id);  // ✗ Collision: unless id-uniqueness is witnessed:
                                //   "two users could share an id — use group,
                                //    prove the key function injective, or group
                                //    and fold each id to its one user or #collision"
```

<!-- DESIGN.md:5280 layer L5: ring L1, word L5 (maxBy), label none; section [sec:tour_collections] 4 -->
```zed
byId = users.group(u -> u.id);  // ✓ type: Id ->? (UserKey -> User)  (the extra level, declared by the word)

// argmax keeps ties honest — keypath integrity forces the policy into the open:
best = scores.maxBy(v -> v);    // (score ->? name -> score) | #none: ALL tied entries kept, #none only when scores is empty
one  = best?.first;             // #none carried; lexicographic: the max-score group, then least name
                                // (first/last descend by each level's order — sec:corner_cases)
```

<!-- DESIGN.md:5291 layer L5: ring L1, word L5 (join), label none; section [sec:tour_joins] 1 -->
```zed
// query projection      (payments : OrderId -> Payment — uniquely keyed,
//                        which is what keeps the join flat, sec:joins;
//                        kind: #inner | #left | #right | #outer, #inner by default)
paid = orders.join(payments, on: #orderId, kind: #left);
     // OrderId -> (Order, Payment | #none) — the pair of sec:joins; absence is a value, not a null row
```

<!-- DESIGN.md:5299 layer L3: ring L3, word none, label none; section [sec:tour_joins] 2 -->
```zed
// iteration projection — the SAME kernel term; the compiler picks the plan
paid = for o in orders {
  payment = payments[o.orderId] else #none;
  (o, payment)                 // the frame's export: the one statement without a `;`
};
```

<!-- DESIGN.md:5307 layer L5: ring L1, word L5 (diff), label none; section [sec:tour_joins] 3 -->
```zed
// anti-join, both ways (same term again)
unpaid = orders.diff(payments, on: #orderId);
```

<!-- DESIGN.md:5312 layer L8: ring L8, word L3 (where), label none; section [sec:tour_joins] 4 -->
```zed
unpaid = orders.where(o -> payments[o.orderId] is #notFound);

// several generators: one level keyed by the tuple of keys; generators that do not depend on each other
// range over the product of their domains — an equality between them in `where` is planned as a join,
// and no predicate is the cross product (shipments : ShipmentId -> Shipment, orderId a field — one order, several shipments)
shipped = for o in orders, s in shipments where o.orderId == s.orderId { (o, s) };   // ((OrderId, ShipmentId)) ->? (Order, Shipment): one level, tuple-keyed

// a domain that mentions another generator's binder nests inside it, as the dependency requires: the
// pairs with i < j, keyed (i, j) — the same family as `for i in 0..<n, j in 0..<n where i < j`
pairs = for i in 0..<n, j in i+1..<n { (i, j) };

// matrix multiply — join on the inner dimension, reduce it away
matmul(positional a: (r -> c -> f64), positional b: (c -> k -> f64)) =
  (a, b) into (r -> k -> c >< (+) -> a[r][c] * b[c][k]);  // shared inner domain c, named by both sources; the float `+` folds on the canonical tree over `c`'s order (sec:joins)
// read as an index expression: the output names the free levels (r, k), the reduced level (c) is summed
// away, and the leaf is the product — einsum's "rc,ck->rk", with the contraction written where it happens
prod = a.matmul(b);
```

<!-- DESIGN.md:5334 layer L6: ring L6, word L6 (::frames), label none; section [sec:tour_loops] 1 -->
```zed
// comprehension — parallel by default
sq = for i in 0..<n { i * i };

// recurrence with a sentinel — compiled to a parallel scan (+ is associative)
cdf[i] = cdf[i-1] + hist[i]  with cdf[-1] = 0;
total  = cdf.last else 0;                // .first/.last: by rank order; | #none when empty

// generations: the only mutable state
sim = loop t {
  while t < maxSteps;                    // a read history needs a proven bound on the steps
  initial pos = p0;                      // sentinel values: the frame before step 0
  initial vel = v0;
  pos' = pos + vel * dt;
  vel' = vel + a(pos) * dt;
  until pos'.x > bound;                  // primes test the new state; bare names the old
};
final   = sim.pos;                       // last generation's value
history = sim::frames;                   // Gen -> { pos: P, vel: V } — the whole trajectory, at most maxSteps frames
steps   = sim::len;

// fixpoint loops need no dirty flags
simplified = loop {
  initial terms = input;
  terms' = simplifyOnce(terms);
  until terms' == terms;
};

// group-boundary processing without the classic off-by-one-flush bug
sessions = events.chunkBy(e -> e.userId);     // key-change splits; last chunk included
report   = sessions.map(s -> summarize(s));
```

<!-- DESIGN.md:5369 layer L3: ring L3, word L3 (where), label none, documentation notation; section [sec:tour_failure] 1 -->
```zed
parse : (Utf8String) -> Config | #syntaxError(..)         // an assumed input, shown as a type — no ';' (sec:lexical)

conf = parse(text) else defaultConfig;
port = parse(text)?.server?.port else 8080;    // ?. carries the union; else disposes of it

results = files.map(f -> read(f)).map(b -> parse(b));
// File -> Config | #ioError | #notFound | #syntaxError(pos)   — bad records flow, tagged, with lineage
good = results.where(r -> r is Config);
bad  = results.where(r -> r is not Config);     // each still knows which file, which wave

amounts = files.map(f -> int(read(f)));        // File -> int | #invalid | #ioError | #notFound
sumAll  = amounts >< (+);                      // int | E | #errs(E ->? E), E = #invalid | #ioError | #notFound:
                                               //   the sum, or every distinct failure, merged; (+) never runs
                                               //   on a failure — the unlifted-carrier rule (sec:reduction)
// All or nothing is the default, and the type says so: nothing is summarized behind
// your back. Where another policy is meant, say what the failures mean:
sumKept   = amounts.where(a -> a is int) >< (+);   // 1: drop errors — visibly
sumZeroed = amounts.map(a -> a else 0) >< (+);     // 2: default them — visibly
badAmounts = amounts.where(a -> a is not int);     // 3: keep them — an ordinary
                                                   //    collection, sized and reported
```

<!-- DESIGN.md:5394 layer L21: ring L20, word L21 (store), label none, documentation notation; section [sec:tour_grammar] 1 -->
```zed
// one declaration: type + parser + serializer (round-trip canonical)
struct KeyVal  grammar { key: Ident  ":"  value: Json }
struct JsonObj grammar { "{"  entries: KeyVal sep ","  "}" }
type   Json = JsonObj | JsonArr | JsonStr | JsonNum | #true | #false | #null;

cfg = Json.parse(bytes);         // Json | #syntaxError(..)  — recovery structural
out = cfg?.serialize;            // entries in parsed order: parse(serialize(x)) == x; ?. carries the union

type Ident = Utf8String matching grammar { alpha (alpha | digit)* };  // typed strings, not regexes
// whitespace: struct grammars (phrase level) skip insignificant whitespace between elements;
// matching grammars (token level, as here) are exact. serialize emits none — the canonical form.

// a binary grammar (a PNG chunk): the format facets of sec:ffi on items, no whitespace skipped;
// n is a stored field, and the type carries data.count == n
struct Chunk grammar {
  n: int with bits(32) with endian(#big)
  kind: u8* with length(4)
  data: u8* with length(n)
  crc: int with bits(32) with endian(#big)
}
// a tagged choice: tag 1 selects Ping, 2 selects Data; distinct tags discharge emission-disjointness
struct Message grammar { tag: u8  body: (Ping | Data) with tagged(tag, 1, 2) }

// tests are data, attached to the definition, run in the dirty cone only
double(positional x) = x * 2       // the `test` clause ends the declaration, so no `;` here
  test { 0 -> 0, 2 -> 4, -3 -> -6 }
law doubleIsSum(x: int) = double(x) == x + x;   // a test over the whole domain: graded, never run (sec:verification)

// ports are the only outside world
main(m: MainArgs) {
  m.stdout <- m.stdin.map(l -> l.upper else "");
}

// a stored collection is a port too; its schema is a build input, matched statically
orders: OrderId ->? { total: rat, note: Utf8String | #none }
  with store(postgres(dbUrl, table: "orders", schema: sql("db/orders.sql")));

n = orders[id]?.note;              // Utf8String | #ioError(…) | #none | #notFound — no db, NULL, no row
// note:  Utf8String                   // ✗ Stored collection whose type and schema disagree: the column is nullable, and #none is missing from the field type
// total: f64                      // ✗ Stored collection whose type and schema disagree: NUMERIC is not a binary float

// facets: units and taint are checked like types
v = 3.0f64 with units("m/s");
t = 2.0f64 with units("s");
d = v * t;                         // d::units == "m"
// e = v + t;                      // ✗ Units that differ where an operation requires equal ones: m/s + s

exec : (Db, Utf8String with taint(#clean)) -> Rows | #sqlError   // a sink's signature, shown as a type
// exec(db, userInput);            // ✗ Taint at a sink whose parameter does not take it: #userInput taint reaches a #clean sink
rows = exec(db, sanitize(userInput));     // ✓ sanitizers are the only taint-removers
```

<!-- DESIGN.md:5501 layer L3: ring L1, word none, label L3; section [sec:type_notation] 1 -->
```zed
// layer L3
priceOf(positional items, positional id) = items[id]?.price * (1 + taxRate);
```

<!-- DESIGN.md:5508 layer L2: ring L2, word none, label none, documentation notation; section [sec:type_notation] 2 -->
```zed
priceOf : (K ->? {price: f64}, K) -> f64 | #notFound
```

<!-- DESIGN.md:5520 layer L20: ring L20, word L20 (serialize), label none; section [sec:power] 1 -->
```zed
// 1 — Deterministic parallel float sum: bit-identical at any core count.
total = readings >< (+);
// Elsewhere: parallel float reduction is nondeterministic unless you build the tree yourself.

// 2 — Scatter and gather are the same computation; the compiler proves it and picks the plan.
histA = words.group(w -> w.len).count;
histB = for n in 0..=maxLen { words.where(w -> w.len == n).count };
// Same kernel term up to the stated domain (law 24): histB's dense domain also states the zero
// buckets (outer-join histA with 0s to convert); the plans converge on the shared part.
// Elsewhere: two different programs, two different performance cliffs, no equivalence check.

// 3 — Edit distance, written both ways, one meaning: memoized recursion or wavefront table.
d[i][j] = min(d[i-1][j] + 1, d[i][j-1] + 1, d[i-1][j-1] + cost(a[i], b[j]))
  with d[-1][j in -1..<b::len] = j + 1, d[i in 0..][-1] = i + 1;  // disjoint pieces: the corner
  // d[-1][-1] = 0 is the first family's j = -1 entry — overlap would be a collision
// The demanded corner pulls (memoized); dense demand pushes (wavefront). Same source.

// 4 — "Inherently serial" text scan, parallelized because the state domain is finite.
state[i] = csvStep(state[i-1], text::codepoints[i])  with state[-1] = #outsideQuotes;
// state : #escape | #inQuotes | #outsideQuotes (finite) — so the compiler reifies
// csvStep into a transition table and runs a parallel prefix scan.

// 5 — First prime above N: speculative parallel search with automatic cancellation.
firstPrime = (for i in n.. { i }).where(isPrime).first;
// Pure ⇒ higher candidates run speculatively and are canceled the instant a lower hit lands.
// Typed `int | #none`: the source is infinite but primality is not the checker's business,
// so a use site still says what an empty selection means (sec:corner_cases).

// 6 — Sessionize a log: the group-boundary/flush-the-last-group bug cannot be written.
sessions = clicks.chunkBy(c -> c.userId).map(s -> Session(start: s.first.time, count: s.count));
// a chunk exists only because a click fell into it (L ≠ ∅), so .first is exact — no #none case

// 7 — Undo, redo, and time travel are field reads, not an architecture.
run  = loop t { while t < edits::len && !closed; initial doc = empty; doc' = doc.patch(edits[t]); };
     // history bounded by edits::len; retained because ::frames is demanded below
past = run::frames[run::len - 2].doc else empty;  // any past state, O(log n), shared

// 8 — A spreadsheet cell is just a memoized value; editing one input reflows in milliseconds.
@memoized report = sales.join(costs, on: #sku).group(((s, c)) -> s.region).map(rows -> rows.map(((s, c)) -> margin(s, c)).sum);
// Edit one row of sales ⇒ exactly the dirty cone recomputes, with provenance for every cell.

// 9 — SQL injection is a compile error, not a code-review hope.
// rows = exec(db, "SELECT * WHERE name = " ++ userName);      // ✗ Taint at a sink whose parameter does not take it: #userInput taint reaches a #clean sink
rows = exec(db, "SELECT * WHERE name = " ++ sanitize(userName));  // ✓ and the sanitizer is auditable

// 10 — Wrong physics doesn't build.
energy = m * v * v / 2;        // energy::units == "J", printed kg m^2/s^2 (J): the alias J is kg m^2/s^2
// e = energy + force;            // ✗ Units that differ where an operation requires equal ones: kg m^2/s^2 (J) and kg m/s^2 (N), ratio m

// 11 — One declaration = type + parser + printer, with round-trip guaranteed.
struct Vec3 grammar { "(" x: f64 "," y: f64 "," z: f64 ")" }
v = Vec3.parse("(1.0, 2.0, 3.0)") else Vec3(x: 0, y: 0, z: 0);
s = v.serialize;                   // "(1.0,2.0,3.0)" — phrase grammars skip input whitespace, serialize emits the canonical none; parse ∘ serialize == id

// 12 — Compute only what's asked: one stats module, demand-pruned.
stats(positional data: [f64]) {
  n = f64(data::len);                // conversion by type application — no cast syntax
  mean = data.sum / n;
  sd   = (data.map(x -> (x - mean)^2).sum / n).sqrt;
  return { mean:, sd: };     // one export, a record display: each field is its own node
}
m = stats(xs).mean;                // sd's sub-graph never runs
// Elsewhere: you split the API, or you pay for everything every call.

// 13 — Invert any finite map in one line — grouping is a type, not a runtime surprise.
whoTeaches = teacherOf as (teacher -> course) into (course -> teacher -> _);   // teacherOf : Teacher -> Course; result Course ->? {Teacher}

// 14 — A tiny service, split into client and server by the compiler.
req: Stream(Query);
resp: Stream(Answer);

main() {
  resp <- req.map(q -> lookup(db, q) else #unknown);
}
// Deploy with a keypath cut: the boundary serializes via struct grammars — RPC without stubs.

// 15 — Exhaustive correctness, free, when domains are small.
@exhaustive romanDigit(n: int[1..=9]) -> Utf8String { … }
  test { 1 -> "I", 4 -> "IV", 9 -> "IX" }
  // @exhaustive: all nine inputs run at build time — totality, the declared
  // properties, and the test table are checked on every one. (A complete
  // expected-output table makes this a full proof; with a partial table,
  // unlisted inputs are verified for totality and properties only.)
  // (@checked is different: it marks representation-capped integers whose
  //  overflow surfaces as a value instead of widening)

// 16 — A ten-hour pipeline survives its bad records and can prove which they were.
out = files.map(read).map(parse).map(transform);
bad = out.where(r -> r is not Row);   // every failure carries file, offset, wave, and cause

// 17 — Declared history, inferred storage: the compiler keeps exactly two frames.
pos[i in 0..<n] = 2*pos[i-1] - pos[i-2] + accel(pos[i-1]) * dt^2
  with pos[-1] = p0, pos[-2] = p0 - v0*dt;
last = pos[n-1] else p0;    // dependence window = 2 ⇒ a two-slot ring; no array exists
// traj = pos::frames;      // demanding the history would turn storage back on — a different plan
// Elsewhere: you hand-rewrite the array into two variables and lose the history option.

// 18 — Indexes are demand: no keyed lookups, no index — the "table" stays a flat run.
report = logs.map(rowCost).sum;       // logs : Id ->? Row, but only ever scanned here:
                                      //   the id index has no dependents — pruned;
                                      //   contents compile to a linear unindexed run
// hot = logs[someId];                // one keyed probe would demand the index, built
                                      //   lazily or eagerly by the cost arithmetic
// Elsewhere: the index exists because the schema says so, and you pay for it either way.

// 19 — Maximum subarray, a non-associative scan, parallelized because its step is affine over (max, +).
cur[i] = max(xs[i], cur[i-1] + xs[i])  with cur[-1] = 0;
best = cur >< max else 0;
// xs : int[0..<n] -> int. The step c -> max(xs[i], c + xs[i]) is the (max, +) affine map
// (a, b) = (xs[i], xs[i]), and two such maps compose to (max(a2, a1 + b2), b1 + b2),
// so cur is a parallel prefix scan (sec:optimizer). Floats do not take this path.
// Elsewhere: Kadane's loop is serial, and its parallel form is a research exercise.

// 20 — A generic JSON decoder, specialized by partial evaluation into a decoder for one struct.
struct User { id: int, name: Utf8String }
u: User | #parseError(..) = Json.decode(text);
// The ascription fixes decode's result type at User (sec:type_resolution, rule 2), and User
// is known at build, so mix specializes decode on it (sec:staging): the generic JSON parser,
// the schema check, and the unpacker into a native struct become one deserializer that reads
// the two fields of User directly into a User, with no intermediate Json tree, and with the
// field names of User compiled into the matcher. text : Utf8String has no finite domain, so mix
// does not specialize on it: the checks on its contents stay in the residual program, and
// #parseError stays in the type.
ok:  User | #parseError(..) = Json.decode("{\"id\": 5, \"name\": \"John\"}");
bad: User | #parseError(..) = Json.decode("{\"id\": \"5\", \"name\": \"John\"}");
// Here the input is a literal, whose domain is a singleton (sec:domains), so the whole call
// runs at build: ok is the constant User(id: 5, name: "John"), and bad is the constant
// #parseError(pos: 7, msg: "expected int for field 'id', got string", expected: ["int"],
// open: [#open(rule: "User", pos: 0)]). Neither residual program contains a parser.
// decode is written in Zed, in the prelude unit Json, with the reads of (sec:introspection):
// T::shape selects the arm, T::fields gives the names and types.
// Elsewhere: a generic decoder reflects on the type at run time (Jackson), or a macro or a
// code generator writes the specialized decoder (serde, protoc), as a second tool.
```
