> [!NOTE]
> **Zed is still under construction and is not yet ready for use, but it is coming soon.**
> Releases will be announced at [x.com/zedlang](https://x.com/zedlang). This page describes the language as it will be when finished.

<p align="center">
  <img src="docs/assets/banner.svg" alt="Zed" width="512">
</p>

Zed is a programming language that looks like ordinary code, but has no variables you overwrite and no statement order you have to get right. A Zed program is a set of definitions: each value says what it depends on, and the compiler works out the rest. Because the compiler can see that whole graph of dependencies, it can run your code in parallel, free memory without a garbage collector, recompute only what changed when an input changes and reject many bugs before the program runs.

- [Notation](#notation): the syntax, words and terms used on this page
- [A first program](#a-first-program)
- [The basics](#the-basics): bindings, functions, numbers, strings, structs, unions, generics, modules
- [Failure is a value](#failure-is-a-value)
- [Collections](#collections): maps, grouping, remapping, reducing, pushing, joins, chunks, matrices
- [Time and repetition](#time-and-repetition): recurrences, loops, methods, running only what's needed
- [The outside world](#the-outside-world): ports, retries, databases, incremental updates
- [Checks at compile time](#checks-at-compile-time): ranges, units, taint, cost
- [Code that runs at build time](#code-that-runs-at-build-time): partial evaluation, reflection, grammars, symbolic math
- [Tests, laws and proofs](#tests-laws-and-proofs)
- [Under the hood](#under-the-hood): error messages, C, memory, parallelism, targets

## Notation

This section lists all the syntax, words and terms the examples on this page use, so you can look up anything you don't recognize. Most of them come back with an example in the tour. If you'd rather start with code, [skip to the first program](#a-first-program) and come back when you need to.

### Conventions on this page

| Form | Meaning |
|---|---|
| `// text` | A comment. |
| `// ✗ rejected` | A commented-out line that the compiler rejects, with the reason. |
| `...` in a **Syntax** line, `x`, `T`, `op`, `pattern`, `fallback`, `#someFailure` | Placeholders for code you would write. In real code, `...` has the one meaning given below. |
| `input:` | A value an example reads that its code doesn't show. The plain-text blocks and tables below an example start with these lines, if it has any, then give each thing it computes under that thing's name. They are not Zed code. |

### Words used throughout

| Term | Meaning |
|---|---|
| map, key, value, entry | A map sends each *key* to a *value*, and a key with its value is an *entry*. |
| level | One layer of keys in a nested map. `a -> b -> v` has the two levels `a` and `b`. |
| keypath | The chain of keys that leads to a value, such as `(a, b)`. |
| struct, field, method | A *struct* is a record of named *fields*, built with `Name(x: 1)`. A *method* is a function you call on a struct with a dot, as in `p.norm`, and its body can read the fields by name. |
| pattern | The part of a `match` arm or a remap that names the shape of a value. |
| failure | An atom in a value's type that says the operation didn't give a result. An atom is a value written `#name`, like an enum value. |
| port | A declared channel to the outside world: a file, socket, clock or database. |
| facet | An extra fact about a value, tracked through every operation at compile time. |

### Definitions and functions

| Syntax | Meaning |
|---|---|
| `name = value;` | A *binding*: gives a name to a value, once. Definitions can come in any order. |
| `name: T = value;` | A binding with a stated type. |
| `name: T;` | Declares a name and its type, with the value given elsewhere: an input, a foreign function, or a map filled by pushes (`name[k] <- v`; see [Less familiar forms](#less-familiar-forms) below). |
| `f(x) = expression;` | A function whose body is one expression. |
| `f(x) -> T { ... }`, `f(x) { ... }`, `f(x) -> T = expression;` | A function with a stated result type, a block body or both. The last expression gives the result, or `return e;`, which ends the block body with the result `e`. |
| `positional x` | A parameter passed by position. Other parameters are passed by name, as in `f(x: 1)`. |
| `y = default` in a parameter list | A parameter that can be left out. |
| `(T) -> U` | The type of a function from `T` to `U`. |
| `x -> expression` | An unnamed function (a lambda). With a type: `(x: rat) -> x + 1r`, where `rat` is an exact rational number and `1r` is the rational 1. |
| `a.f(b)`, `5.double` | A call with the dot: `a.f(b)` is `f(a, b)`, and `5.double` is `double(5)`. |
| `f(x, ...)` | A call that leaves the remaining named parameters open, and gives back a function that takes them. |
| `(+)` | An operator used as a function. |
| `x, y = e;` | Binds each name to a part of a result that has several parts. |
| `field:` in `{ mean:, sd: }` or `Circle(radius:)` | Short for `field: field`. In a pattern it reads the field into a name of the same spelling. |
| `this` | Inside a method: the value the method was called on. |
| `if c { a } else { b }` | A choice between two values. |
| `match x { pattern -> value, ... }` | Picks the arm whose pattern fits `x`. The arms must cover every case. |
| `for x in a { ... }`, `for x in a, y in b where c { ... }` | Builds a map with one entry per element, or per combination the `where` lets through. |
| `loop { ... }`, `loop t { ... }` | A repeated step, with `t` as its optional step counter. The loop is a value holding the final state and the history. |
| `until c;`, `while c;` | Stop conditions of a loop: `until` is tested after each step, `while` before it. |
| `x' = e` | The value of `x` in the next step of a loop or the next version of a struct. See [Less familiar forms](#less-familiar-forms) below. |
| `x' = e with x = start` | The same, with the value of `x` before the first step. |
| `x[i] = e with x[-1] = start;` | A recurrence: an array defined by an equation, with its boundary value at the index just below the first. See [Less familiar forms](#less-familiar-forms) below. |
| `i in 0..` inside `d[i in 0..]` | This entry is defined for every `i` in the range, here from 0 up. |
| `x*.method()` | A call in a loop body that also replaces `x` in the next step. See [Less familiar forms](#less-familiar-forms) below. |
| `mutable x = e;` | A loop variable with the starting value `e`, which keeps its value in any step that doesn't write `x'`. |
| `test { input -> output, ... }` | A table of test cases attached to a definition, run at build time. |
| `law name(x: T) = expression;` | A claim that a `bool` (true or false) expression holds for every `x`. |
| `import a.b;`, `import a.b as c;`, `import a.b.{x, y};` | Imports a module (one source file) whole, under another name, or by listing names. |
| `local` | Keeps a definition private to its file. |
| `main(input: T) -> (output: U) { ... }` | A program's entry point. Its parameters are input ports and its results are output ports. |
| `@name` | An annotation: a claim or request the compiler acts on or checks. They are listed below. |

### Operators

| Syntax | Meaning |
|---|---|
| `+ - *` | Arithmetic. `*` also scales a vector or matrix by a number. |
| `/` | Division on `f64` (a 64-bit floating-point number) and `rat` (an exact rational number). It does not apply to `int` (an integer). |
| `a div b`, `a mod b` | Integer quotient and remainder. |
| `**` | Power. |
| `== != < <= > >=` | Comparison. `==` compares structure, by value. |
| `\|\|` | Logical or. |
| `a ++ b` | Joins two strings or lists. |
| `x in s` | True if `x` is a member of `s`. |
| `x is T`, `x is not T` | Tests whether a value has a type. |
| `m[k]`, `p.x`, `f(x)` | Lookups, in a map, a struct and a function. |
| `x::word` | Reads a fact about `x`, such as its length or its type's fields. The facts are listed below. |
| `x else d` | Gives `d` in place of a failure. `x else #a -> d` replaces only the atom `#a`, which is like an enum value. |
| `x?.field` | Reads a field if there is one, and passes a failure along if there isn't. |
| `m >< op` | *Reduces* the innermost level of `m` with the operator `op`. See [Less familiar forms](#less-familiar-forms) below. |
| `m >< op else d` | The same, with `d` as the answer for an empty collection. |
| `unordered` after `m >< op` | Gives up the floating-point result that's identical at any core count, in exchange for speed. |
| `m as (pattern) into (pattern)` | A *remap*: names the shape `m` has and the shape you want. See [Less familiar forms](#less-familiar-forms) below. |
| `k >< op` inside a pattern | Collapses the level `k` with `op`. |
| `desc k`, `asc k` | Orders by `k`, high to low or low to high. In a remap's key position it adds a level keyed by rank, where equal values share one. |
| `_` in a pattern | Drops the value at that place. |
| `name <- v`, `name[k] <- v` | Pushes a value out of a port, or into one key of a map. See [Less familiar forms](#less-familiar-forms) below. |
| `e with name(args)` | Attaches a *facet* or a port setting to a value or type. They are listed below, and facets are explained in [Less familiar forms](#less-familiar-forms) below. |
| `x with { field = value }` | A copy of a struct with some fields changed. |

### Less familiar forms

Most languages have nothing quite like these forms, so each one gets an example here and a comparison with the code you would write elsewhere.

**`#name`: an atom.** An atom is like an enum value that you can write without declaring an enum. Writing `#tooYoung` anywhere is enough. If a function can return an atom, the atom becomes part of the function's result type, in a union (a type that allows any of several kinds of value) with whatever else it can return.

```zed
// positional: callers pass age by position, as checkAge(30), and not by name, as checkAge(age: 30).
checkAge(positional age: int) = if age < 18 { #tooYoung } else { age };

a = checkAge(30) else 18;
b = checkAge(15) else 18;
```

```text
checkAge(15) = #tooYoung, a = 30, b = 18
```

The result type of `checkAge` is `int | #tooYoung`, a value that is either an `int` or that atom, and you can write it out or let the compiler work it out. This is how Zed reports failure: where another language would throw an exception or return null, a Zed function returns an atom, and the type says so until the caller handles it, here with `else`. When you do want a fixed set of names, as with an enum, give the union a name: `type Light = #red | #amber | #green;`.

**`x' = e`: the next value of a variable.** In a loop, `x` is the value from the previous step and `x'` is the value this step writes for the next one. `with x = start` gives the value before the first step.

```zed
fib = loop t {
  while t < 5;
  a' = b with a = 0;
  b' = a + b with b = 1;
};
```

```text
fib.a = 5, fib.b = 8, fib::len = 5
```

In Python this is `a, b = b, a + b`, and in C it needs a temporary. In Zed, writing `a'` doesn't change `a`, so the second line still reads the old `a` and the two lines could be swapped. Each step writes each variable once. `loop t` names the step counter `t`, and `while` is tested before each step. The loop is itself a value: `fib.a` is the final `a`, and `fib::len` is the number of steps.

**`x*.method()`: a call that also replaces `x`.** A method can write a primed field, such as `n' = n + by`, which gives that field's value in a new struct. It returns the new struct along with its result and leaves the old one alone. In a loop, the `*` makes that new struct the value of `x` in the next step.

```zed
struct Counter { n: int }

Counter.bump(positional by) -> int {
  n' = n + by;
  return n;
}

run = loop {
  mutable c = Counter(n: 0);
  prev = c*.bump(3);
  until prev >= 6;
};
```

```text
step 0: prev = 0, next c.n = 3
step 1: prev = 3, next c.n = 6
step 2: prev = 6, next c.n = 9
run.c.n = 9, run::len = 3
```

`prev = c*.bump(3);` is short for `c', prev = c.bump(3);`. It has the same effect as `cNext, prev = c.bump(3);` followed by `c = cNext` at the end of the step, where `bump` has no side effects and returns a changed copy of `c` along with its result. So it reads like a mutating method call in Java or Python, with two differences. The rest of the step still reads the old `c`. And a step can write `c'` only once, so two calls in one step have to be one chain: `a, b = c*.bump(1).bump(2);`. Without the `*`, a call never changes a value you hold: `c.bump(3);` alone is rejected because its result would be thrown away. On a value bound with `=`, `c*.bump(3)` is rejected because there is no next step to write.

**`x[i] = e with x[-1] = start`: an array defined by an equation.**

```zed
running[i] = running[i-1] + xs[i] with running[-1] = 0;
```

```text
input: xs = [3, 1, 4]
running = [3, 4, 8]
```

Elsewhere this is a `for` loop that fills an array in order. Here it's a statement about every entry, and the compiler reads the dependencies and picks the order. `running[-1]` is the starting value that a read just below the first index finds, and it isn't an entry of the result. A boundary can cover many entries: `d[i in 0..][-1] = i + 1` defines `d[i][-1]` for every `i` from 0 up.

**`m >< op`: reduce a level.**

```zed
readings = [2, 5, 3];
total = readings >< (+);
```

```text
total = 10
```

This is `reduce` or `fold` elsewhere, but you give no direction, because the work can be split across cores in any grouping. That's why `op` has to be safe to regroup, except on floating-point values, which have their own rule (see [Reducing](#reducing) below). On a nested map it collapses only the innermost level: with `sales: region -> sku -> amount`, a map from each region to a map from each `sku` (a product code) to an amount, `sales >< (+)` gives one total per region. Inside a remap pattern, shown next, `sku >< (+)` names the level to collapse.

**`m as (pattern) into (pattern)`: a remap.**

```zed
transposed = matrix as (r -> c -> v) into (c -> r -> v);
```

```text
input: matrix = [[1, 2, 3], [4, 5, 6]]
transposed = [[1, 4], [2, 5], [3, 6]]
```

Elsewhere this is a pair of nested loops that set `out[c][r] = matrix[r][c]`, or a pivot in a data frame library. `as` gives a name to each level of keys and to the value, and `into` draws the shape you want using those names. A remap can't overwrite a value: if two values would land on one key, the compiler rejects it until you say what should happen.

**`name[k] <- v`: a push into a map.**

```zed
hist: int ->? int with reducer((+));
for w in words { hist[w.len] <- 1; };
```

```text
input: words = ["a", "to", "be", "not"]
pushes: hist[1] <- 1, hist[2] <- 1, hist[2] <- 1, hist[3] <- 1
hist = { 1 -> 1, 2 -> 2, 3 -> 1 }
```

`int ->? int` is a map from `int` to `int` that may lack some keys, `with reducer((+))` says that values pushed to one key are added, and `w.len` is the length of `w`. This looks like `hist[k] += 1` on a dictionary, but nothing is read back or overwritten. `hist` has one value, which is all its pushes merged per key by the reducer, so pushes can come from many places in the program.

**`e with units(...)`: a facet, an extra fact about a value that the compiler tracks.**

```zed
v = 3.0 with units("m/s");
t = 2.0 with units("s");
d = v * t;                 // has units "m"
// e = v + t;              // ✗ rejected: m/s + s
```

In other languages a unit usually takes a wrapper type such as `Meters`, with its arithmetic written by hand. A facet leaves the value an `f64`, and the compiler follows the label through each operation.

### Values and literals

| Syntax | Meaning |
|---|---|
| `42`, `1.5`, `3r`, `2n` | An `int`, an `f64`, a `rat`, and a generic number that takes whichever number type its use needs, so `inc(x) = x + 1n;` works on all three. |
| `"text"`, `"${e}"` | A `Utf8String` (a string of UTF-8 text), with `e` written into it. |
| `#name`, `#name(args)` | An *atom*: like an enum value that needs no enum declaration. It can carry data, its payload. See [Less familiar forms](#less-familiar-forms) above. |
| `[a, b, c]` | An array, whose keys are `0`, `1`, `2`. |
| `{ k -> v, ... }` | A map, written out. |
| `{ a, b }` | A set. |
| `{ x: 1, y: 2 }`, `Name(x: 1)` | A struct value, without and with a declared name. |
| `(a, b)` | A tuple: a fixed number of values, possibly of different types. |
| `a..<b`, `a..=b`, `a..` | Ranges: excluding `b`, including `b`, and with no upper end. |

### Types

| Syntax | Meaning |
|---|---|
| `int` | A mathematical integer. It can't overflow. |
| `char32` | A Unicode code point (the number Unicode assigns to a character), distinct from an integer. `char32("Z")` constructs one. |
| `int[a..=b]`, `int[a..]` | An integer in a range. |
| `f64`, `rat`, `bool`, `u8` | A 64-bit floating-point number, an exact rational number (a fraction of two integers, never rounded), true or false, and an integer from 0 to 255. |
| `Utf8String`, `U8String`, `Utf16String`, `Utf32String` | String types. `Utf8String`, `Utf16String` and `Utf32String` hold checked text in that encoding, and `U8String` holds 8-bit units with no encoding checked. String literals are `Utf8String`. |
| `K -> V` | A map with a value at every key of `K`. A function type too. |
| `K ->? V` | A map that may lack some keys of `K`, so a lookup can give `#notFound`. |
| `a -> b -> v` | A nested map: `a -> (b -> v)`. Each arrow adds one *level* of keys. |
| `[T]` | An array of `T`. |
| `[T; n]`, `[T; r, c]` | A vector of length `n` and a matrix of `r` rows and `c` columns. |
| `A \| B` | A *union*: a value that is either an `A` or a `B`. Its *members* are `A` and `B`. |
| `T` (capitalized and otherwise undefined) | A type variable, when used at least twice in a signature, or in the signature and the body. |
| `struct Name { field: T, field: T = default }` | A record type. Its fields can have defaults. |
| `Name.method = e;`, `Name.method() { ... }` | A method: a function with an implicit first parameter, whose fields are in scope. |
| `type Name = T;`, `type Name(T) = ...;` | A name for a type, with or without type parameters. |
| `interface Name { ... }` | A list of fields and laws. Any value that has them fits it. |
| `grammar { ... }` | A parser and serializer in one definition, on a struct or after `matching`. |
| `T matching grammar { ... }` | The values of `T` that a grammar accepts. |
| `"("`, `x: T`, `a sep b`, `a*`, `digit` in a grammar | Literal text, a field, a list of `a` separated by `b`, zero or more of `a`, and one decimal digit. |
| `Files`, `Lines`, `Stream(T)` | Port types: files by path, lines of text, and a sequence of values over time. |

### Failure atoms

| Atom | Meaning |
|---|---|
| `#notFound` | A lookup found no entry. |
| `#none` | There is nothing here: an empty selection, the missing side of a left join (a join that keeps every entry of its left input), or a NULL column in a database. |
| `#empty` | A reduction with nothing to reduce. |
| `#collision` | Two entries landed on one key, where a claim that the key is unique was wrong. |
| `#divByZero` | A division by zero: `div` or `mod`, or `/` on `rat`. |
| `#inexact` | A number conversion that can't keep the exact value. |
| `#invalid` | A value failed a condition or a type check at run time, as with `x.refine(p)`, listed below. |
| `#syntaxError`, `#parseError` | Text doesn't parse. |
| `#ioError`, `#dbError`, `#timeout` | A port failed, a database failed, or a deadline passed. |

Other atoms on the page, such as `#red` or `#goNs`, are data the examples define. `#left`, `#orderId`, `#fixed`, `#big`, `#clean` and `#userInput` are arguments to the words they follow. `#block`, `#dropOldest` and `#full` say what a full queue does, and `#unbounded` is what a cost reads when no bound could be proved.

### Words from the standard library

| Word | Meaning |
|---|---|
| `m.map(x -> e)` | Replaces each value and keeps the keys. |
| `m.where(x -> c)` | Keeps the entries whose value passes, with their keys. |
| `m.group(x -> key)` | Adds a level of keys above the existing ones. |
| `m.rekey(x -> key)` | Replaces the key. The compiler needs evidence that the new key is unique. |
| `m.sort(desc x -> x)` | Orders by the given key. |
| `m.rank` | Flattens an ordered nested map into one list numbered in that order. |
| `m.chunkBy(x -> key)` | Splits an ordered collection wherever the key changes. |
| `m.flatMap(x -> list)` | Maps each value to a list, with the list's positions as a new level. |
| `a.join(b, on: #field, kind: #left)` | Pairs entries of `a` and `b` on a field. |
| `a.diff(b, on: #field)` | The entries of `a` that have no match in `b`. |
| `.count`, `.sum` | Reduces the innermost level to its number of entries, or to their sum. |
| `.first`, `.last` | The value at the lowest or highest key, in the collection's order. |
| `.foldl(init, op)`, `.foldr` | A fold from the left or the right, for an operator that can't be regrouped. |
| `m.allOk` | `m` if no entry holds a failure, and otherwise the failures. |
| `.image`, `.union` | The set of a map's values, and the union of two sets. |
| `p.implies(q)` | Logical implication. |
| `x.refine(p)` | `x`, or `#invalid` if the condition `p` fails. |
| `min`, `max`, `sqrt`, `log`, `pi` | The usual math functions and constant. `min` and `max` work as operators for `><`. |
| `fs[path]`, `read(path)` | Reads a file from the port `fs`; `read` is short for that lookup. |
| `.split`, `.lower`, `.len` | Splits a string on a separator, lowers its case, and gives a length. |
| `a.matmul(b)`, `dot`, `cross` | Matrix product, dot product and cross product. |
| `f64(n)`, `int(s)`, `char32("Z")` | Checked conversions between types. |
| `stdout` | The port for standard output. `<-` writes to it. |
| `x.patch(edit)` | Applies an edit to a map or document and gives the new version. |
| `T.parse(s)`, `x.serialize` | A grammar's parser and serializer. |
| `Json.decode(s)` | Decodes JSON into the type expected at the call. |
| `expand`, `derivative`, `compile` | Rewrites a function's source, differentiates it, and turns source back into a function. |

### Facts read with `::`

| Syntax | Meaning |
|---|---|
| `x::len` | The number of entries, or of steps in a loop. |
| `run::frames` | Every step of a loop. |
| `text::codepoints`, `text::u8` | A string viewed by code point or by UTF-8 unit, which is one byte of its encoding. |
| `T::fields`, `T::shape`, `T::values` | A type's fields, its structure, and the members of a set of atoms. |
| `x::constraints` | What the compiler knows about a value. |
| `f::source` | A function's source, as a value. |
| `f::cost`, `f::depth` | Upper bounds on a function's work (its total number of operations) and parallel depth (the longest chain of operations that must run one after another). |

### Annotations

| Annotation | Meaning |
|---|---|
| `@associative`, `@commutative` | Claims that an operator can be regrouped or reordered. |
| `@ensure` | Forbids a run-time check in this definition: the condition has to be proved instead. |
| `@injective` | Claims that a function never gives two inputs the same result. |
| `@memoized` | The build fails if this value isn't kept for reuse. |
| `@cost(b)`, `@fused`, `@noalloc`, `@preallocated` | Performance claims the build checks: a work bound, no intermediate collection, no memory beyond registers, a bounded footprint reserved at entry. |
| `@exhaustive` | Run the tests on every input of a finite domain. |
| `@proved`, `@strict`, `--strict` | Make the build fail on a law that isn't proved. `--strict` is a compiler flag. |
| `@foreign("lib", "symbol")`, `@export("c", "symbol")` | Calls a C function, and makes a Zed function callable from C. |
| `@stateless` | A promise that a foreign function has no state, so it can be retried. |
| `@hash` | The content hash that pins an import. |

### Facets and port settings, written with `with`

| Word | Meaning |
|---|---|
| `units("m/s")` | A physical unit, checked through arithmetic. |
| `taint(#label)` | A label that follows a value through the program. |
| `reducer(op)` | How values pushed to one key of a map merge. |
| `store(...)`, `postgres(...)`, `kv(...)`, `file(...)`, `sql(...)` | Makes a map a stored table: in Postgres, in a key-value store or in a file, with a schema read from an SQL file. |
| `timeout(d)`, `retry(n, backoff: b)`, `bound(n, overflow: policy)` | A deadline, repeat attempts with a wait `b` between them, and a queue's size limit with what happens when it is full. |
| `bits(n)`, `endian(#big)`, `length(n)` | Binary layout in a grammar: a field's width, its byte order, its element count. |

### Terms

| Term | Meaning |
|---|---|
| rank | A position in an order: a key `0`, `1`, `2`, and so on. Values that tie share a rank when `desc` or `asc` adds the level. |
| remap | Changing a map's shape by moving, adding or dropping levels. |
| reduce, reduction, fold | Merging the values of a level into one, with an operator. |
| domain | The keys or inputs a map or function is defined on. |
| bounds check | The run-time test that an index is in range. |
| schema | The columns and types a database table declares. |
| parser, serializer | A parser turns text into a value, and a serializer turns a value back into text. |
| edit distance | The fewest single-character changes that turn one string into another. |
| maximum subarray | The run of neighboring entries in an array with the largest sum. |
| data race | Two threads using the same memory at once, with at least one of them writing. |
| rope | A string or list stored as a tree of pieces, so joining two takes constant time. |
| taint | A label for where a value came from, such as user input. |
| wave | A batch of new input values passing through the program's graph. |
| work, parallel depth | *Work* is the total number of operations. *Parallel depth* is the longest chain of them that must run one after another. |
| effect system | Type annotations that record a function's side effects. |
| memoize | Keep a result so that later uses don't compute it again. |
| law | A claim about your code, which the compiler tries to prove and otherwise tests. |
| associative, commutative | `(a op b) op c == a op (b op c)`; and `a op b == b op a`. |
| identity | A value that leaves the other operand unchanged, such as 0 for addition or 1 for multiplication. |
| `Monoid`, `CommRing` | Interfaces from the library for algebraic structures: an associative operator with an identity; and addition with multiplication, where multiplication commutes. |
| grade | How far the compiler got with a law: for example proved, tested or assumed. |
| partial evaluation | Running the parts of a program whose inputs are known at build time. |
| specialize | Produce a version of a function for known types or values, with the generic steps gone. |
| decidable | Answerable by an algorithm that always finishes. |
| linear arithmetic | Sums of variables times constants, with comparisons. |
| SMT solver | A general automated theorem prover, as used by many verification tools. |
| fixpoint | A value that one more step doesn't change. |
| model checking | Checking a property on every state a system can reach. TLC is a widely used model checker. |
| liveness, fairness | *Liveness*: something good eventually happens. *Fairness*: an assumption that no ready action of the environment is put off forever. |
| safe to repeat, idempotence | Doing it twice has the same effect as doing it once. |
| hedged request, circuit breaker, failover | Sending a second copy of a slow request; refusing calls for a while after repeated failures; switching to a replacement server. |
| scan, parallel scan | A computation that gives each running result, such as the running totals of a list. A parallel scan does this on many cores at once. |
| hash join, merge join | Two standard ways to compute a join without comparing every pair. |
| exact reference counting | Freeing a value when a count of its users reaches zero, with no count left too high by cycles. |
| arena | A block of memory whose contents are all freed together. |
| id-indexed graph | A graph whose nodes are stored in a table and refer to each other by key. |
| intermediate representation | The form a compiler holds a program in, between source code and machine code. |
| kernel | The small core that the rest of a compiler is built on. |
| distributed dataflow | Running a program across many machines, with data sent between them along its dependency graph. |
| back end | The part of a compiler that produces code for one target. |
| MLIR, LLVM, Clang | Standard compiler infrastructure, and the C compiler built on LLVM. |
| WebAssembly | A portable binary format that runs in browsers and elsewhere. |
| hardware synthesis | Producing a circuit design in place of machine code. |

## A first program

Here is a complete program. It splits a file on spaces, counts each word, and prints the counts, most common first.

```zed
main(fs: Files) -> (stdout: Lines) {
  text = fs["input.txt"] else "";
  counts = text.split(" ").group(w -> w.lower).count;
  lines = counts as (w -> n) into (desc n -> w -> "${w}: ${n}");
  stdout <- lines.rank;
}
```

`main`'s parameters and results are *ports*, channels to the outside world: here `fs` reads files and `stdout` prints. `group` collects the words by their lowercase form (`w -> w.lower` is an unnamed function), and `.count` turns each group into its size. The `as ... into ...` line reshapes that table: `desc n` sorts by count, `w` stays as a second level of keys below it so equal counts don't collide, and each value becomes a line of text, with `"${w}: ${n}"` filling in `w` and `n`. `.rank` flattens the nested table into a list numbered in that order, and `<-` writes the lines out.

These tables show the data after each step, for a file whose whole text is `to be or not to be`. Each column but the last is one level of keys, and the last column holds the values. Where a table has several columns after its keys, they are parts of one value, or an input shown beside its result. A key is printed once and covers every row inside its box, and rows are listed in key order. This page draws most of its data-shaping examples this way.

```text
text.split(" ")          .group(w -> w.lower)          .count
+---+-----+              +---------+---+-----+         +-----+---+
| i | w   |              | w.lower | i | w   |         | w   | n |
+===+=====+              +=========+===+=====+         +=====+===+
| 0 | to  |              | be      | 1 | be  |         | be  | 2 |
| 1 | be  |              |         | 5 | be  |         | not | 1 |
| 2 | or  |              +---------+---+-----+         | or  | 1 |
| 3 | not |              | not     | 3 | not |         | to  | 2 |
| 4 | to  |              +---------+---+-----+         +-----+---+
| 5 | be  |              | or      | 2 | or  |
+---+-----+              +---------+---+-----+
                         | to      | 0 | to  |
                         |         | 4 | to  |
                         +---------+---+-----+

as (w -> n) into (desc n -> w -> "${w}: ${n}")          .rank
+------+-----+--------+                                 +---+--------+
| rank | w   | line   |                                 | i | line   |
+======+=====+========+                                 +===+========+
| 0    | be  | be: 2  |                                 | 0 | be: 2  |
|      | to  | to: 2  |                                 | 1 | to: 2  |
+------+-----+--------+                                 | 2 | not: 1 |
| 1    | not | not: 1 |                                 | 3 | or: 1  |
|      | or  | or: 1  |                                 +---+--------+
+------+-----+--------+
```

The program doesn't mention threads, locks or allocation. The compiler can run the grouping on all your cores, and the output is the same, bit for bit, on one core or on sixty-four. A missing file can't crash the program either: the type of `fs["input.txt"]` says the read can fail, and the `else` says what to do when it does.

Three more short examples from the tour below. A name a snippet doesn't define is an input you can assume:

```zed
// Two values landing on one key is a compile error, never a silent overwrite.
// totals = sales as (region -> sku -> amount) into (region -> amount);   // ✗ rejected
// Say how they merge: add the amounts for each region.
totals = sales as (region -> sku -> amount) into (region -> sku >< (+) -> amount);

// Edit distance, the fewest single-character changes between two strings: the equation and its boundary.
// The compiler picks the table and the fill order.
d[i][j] = min(d[i-1][j] + 1, d[i][j-1] + 1, d[i-1][j-1] + cost(a[i], b[j]))
  with d[-1][j in -1..<b::len] = j + 1, d[i in 0..][-1] = i + 1;

// A database table, checked against its SQL schema at build time. `rat` is an exact rational number.
orders: OrderId ->? { total: rat, note: Utf8String | #none }
  with store(postgres(dbUrl, table: "orders", schema: sql("db/orders.sql")));
```

In these, `><` merges the values at one key, `min` gives the smallest of its arguments, `b::len` is the length of `b`, the `with` after the equation gives the values at the edge of the table, `->?` says a key may be absent, `Utf8String` is UTF-8 text, and the atom `#none` marks a missing note. The tour covers each of them.

Zed exists because many systems already recover a graph of values from ordinary code: spreadsheets, optimizing compilers, Spark, build systems, reactive UI frameworks and out-of-order CPUs. In Zed the graph is the program, so one compiler handles parallel scheduling, memory management, incremental updates and many correctness checks from one structure. This doesn't have to make programs longer: the word-count program above is about as long as the same program in Python.

The rest of this page is a tour of the language. Each stop opens with a line saying what the feature does and lists its syntax. Most then give an example, explain it and show its inputs and results. Snippets stand alone unless they say otherwise. A commented-out line marked ✗ is one the compiler rejects.

## The basics

### Bindings

A binding gives a name to a value.

**Syntax:** `name = value;` or `name: type = value;`

```zed
total = price * quantity;
price = 12;
quantity = 3;
port: int[1..=65535] = 8080;
```

```text
total = 36, port = 8080
```

A name is bound once. It can't be reassigned, and it can be used above the line that defines it, as `price` is here: the order of definitions doesn't matter, only what depends on what. Because a name has one value, you never have to ask what it holds at this point in the program, and the compiler can read the dependency graph straight from the text. The type is optional, and it can be more exact than in most languages. `int[1..=65535]` means an integer in that range, and the compiler checks it.

### Functions

A function is a definition with parameters, and a call can name its arguments, chain with dots or leave some open.

**Syntax:** `f(positional x, y = default) = expression;` or `f(...) -> type { ... }`

```zed
// positional: passed by position, as in double(5). Other parameters are passed by name.
double(positional x) = x * 2;

// -> int states the result type. A { } body gives its last expression, and if gives a value.
clamp(positional v, positional lo, positional hi) -> int {
  if v < lo { lo } else if v > hi { hi } else { v }
}

// Utf8String is UTF-8 text, and ++ joins strings. punct = "!" is a default value.
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

Parameters are passed by name unless you mark them `positional`, so a call site says what its arguments mean. Any function can be called with a dot, so `5.double` is `double(5)`, pipelines read left to right, and adding a step to a pipeline doesn't mean extending a class. A `...` in a call leaves the remaining named parameters open and gives you back a function. Parameter types can usually be left out, and the compiler infers them from how the body uses the parameter. `x * 2` takes an `int`; `x * 2n`, with the generic number `2n`, would take any number type.

### Numbers

Zed has exact integers, rational numbers (fractions of two integers) and 64-bit floating-point numbers (`f64`), and it never converts between them on its own.

**Syntax:** `42`, `1.5`, `3r`, `a / b`, `a div b`, `f64(n)`

```zed
big = 2 ** 100;              // no overflow; this is the exact integer
third = 1r / 3r;             // an exact rational
half = 1.0 / 2.0;            // f64
q = 7 div 2;                 // 3
ratio = f64(q) / 2.0;        // conversions are written out
// bad = q + 1.5;            // ✗ rejected: int + f64
```

```text
big   = 1267650600228229401496703205376
third = exactly one third
half  = 0.5, q = 3, ratio = 1.5
```

An `int` is a mathematical integer. It can't overflow, because the compiler picks its machine representation from the range it can prove, and that is a plain machine word wherever a word is enough. So overflow bugs are gone, without the cost of big integers where the range is known. `/` works on fractional types, and integers divide with `div` and `mod`. A `rat` is an exact rational number, a fraction of two integers that is never rounded. The suffix `r` marks a `rat` literal, so `0.1r + 0.2r == 0.3r` is true. Mixing `int` and `f64` is a compile error until you write `f64(n)`, because a silent conversion is how a large integer gets rounded with nobody noticing. That cast is checked, so its type also includes the failure value `#inexact` unless the compiler can show the value fits exactly.

### Strings

A string's type says how its text is stored, and you say what you index it by, such as *code points*, the numbers Unicode assigns to characters.

**Syntax:** `"text"`, `"${expression}"`, `a ++ b`, `text::codepoints[i]`

```zed
name = "Zed";
line = "total: ${2 + 3}";            // "total: 5"
title = "never" ++ "the" ++ "less";
z = name::codepoints[0];             // the first code point
```

```text
line = "total: 5", title = "nevertheless", z = char32("Z")
```

String literals are UTF-8. `Utf8String`, `Utf16String` and `Utf32String` are separate types, one per encoding, and `U8String` holds 8-bit units with no encoding checked. You pick what you index by, such as code points (of type `char32`) or UTF-8 units, through a named view read with `::`, like `text::codepoints` or `text::u8`, and a `U8String` has no code point view. A bare `text[i]` is rejected, because what position `i` means and what it costs depend on the encoding, and code that assumes one character per position tends to break on the first non-English text. `++` builds a rope (a tree of string pieces) in O(1), so joining strings in a loop doesn't go quadratic.

### Structs

A struct is a record of named fields, compared by value and copied with changes.

**Syntax:** `struct Name { field: type, field: type = default }`, `Name(field: value)`, `x with { field = value }`, `Name.method = expression;`

```zed
struct Point { x: f64, y: f64 }
struct Circle { center: Point, radius: f64 = 1.0 }

p = Point(x: 1.0, y: 2.0);
moved = p with { x = 3.0 };
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

Constructors take their arguments by name. `with` makes a copy with some fields changed, and when the compiler can see the original isn't used again, the copy is an update in place with no allocation. A method like `norm` is a function with an implicit first parameter whose fields are in scope. Two ordinary struct declarations with the same fields are the same type. There are no classes, no inheritance and no object identity. A struct is just a value, so nothing can change it behind your back, and the compiler is free to copy it or share it.

### Atoms, unions and match

An atom is like an enum value that needs no declaration, a union is a choice of types, and `match` takes a union apart.

**Syntax:** `#name`, `#name(args)`, `type T = A | B`, `match x { pattern -> value, ... }`

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

```text
input: Circle with radius 2.0, Rect from (0.0, 0.0) to (3.0, 2.0), #red
area of the Circle = 4 pi, about 12.566
area of the Rect   = 6.0
next(#red)         = #green
```

In a `match` arm, `Circle(radius:)` matches a `Circle` and binds its `radius` field to that name. If a function can return an atom, the function's result type includes it in a union. Atoms with payloads (data carried inside the atom), such as `#c(f64) | #f(f64)`, tell apart values of the same shape. A `match` must cover every case, so when you add a member to `Light`, the compiler points you to each `match` that doesn't handle it yet. If the compiler can't establish that, it shows a value no arm handles or the region it could not resolve. An arm that earlier arms already cover is also rejected.

### Generics and interfaces

Generic code uses type variables with no declaration, and an interface describes what a value must have.

**Syntax:** `type Name(T) = ...`, `interface Name { ... }`

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

`[T]` is an array of `T`, `++` joins arrays as it joins strings, and `s.last` is the last element, or `#none` if there isn't one. An unbound capitalized name that is used at least twice in a signature, or in the signature and the body, is a type variable. Written only once, it is treated as a typo and rejected. Interfaces are structural: any value on which `name` resolves to a `Utf8String` fits `Named`, with no `implements` clause, so a type can fit an interface its author never heard of. An interface can also hold laws, claims about its operations that the compiler proves or tests, so the algebra behind `><` (the parallel reduction covered below), from `Monoid` (an operator that can be regrouped, with an identity value that leaves the other operand unchanged) to `CommRing` (rules for addition and multiplication, including `a * b == b * a`), is ordinary library code.

### Modules

Each file is a module, and an import names what it brings in.

**Syntax:** `import a.b;`, `import a.b as c;`, `import a.b.{x, y};`, `local`

```zed
import geometry.shapes.{Point, dist};

far = dist(Point(x: 0.0, y: 0.0), Point(x: 3.0, y: 4.0));
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

`parse: ...;` declares a function and its type, with the body elsewhere, and the `pos` in the atom says where the parse failed. There are no exceptions and no null, because in most languages both are ways to fail that a function's type doesn't mention. In Zed the type lists every failure a call can give, and the compiler follows each one to where it is handled. `else` replaces a failure with a fallback, and `?.` reads a field if there is one and passes the failure along if there isn't. An atom of a named union, such as `Light`, is data and not a failure, so `else` keeps it unless you name it: `x else #red -> #green`.

A `Config | #syntaxError` is not a `Config`. A lookup's failure passes through arithmetic and calls, so if `m[k]` looks up a key that a map `m` may lack, `1 + m[k]` has type `int | #notFound`. The failure stays in the type until you handle it. A reduction, which merges many values into one (covered below), is stricter: it is rejected if its operator might be applied to a failure it does not handle, since failures at many keys can't become one result unless you say how.

The compiler also adds a failure only where it can't rule it out. `a div b` has type `int` when `b` can be shown never to be zero, and `int | #divByZero` when it can't. `xs[i]` is plain `T` when `i` is known to be in range. Prove the bound, and the failure and its run-time check both disappear.

### Failures in a pipeline

Failures sit in collections as ordinary values, so you can test for them and choose what to do with them.

**Syntax:** `r is T`, `r is not T`, `m.allOk`

```zed
results = files.map(f -> read(f)).map(b -> parse(b));

good = results.where(r -> r is Config);
bad = results.where(r -> r is not Config);
```

```text
input: files     .map(f -> read(f))          results
+---+-------+    +---+---------------+       +---+----------------------+
| i | file  |    | i | value         |       | i | value                |
+===+=======+    +===+===============+       +===+======================+
| 0 | a.cfg |    | 0 | a.cfg's bytes |       | 0 | Config               |
| 1 | b.cfg |    | 1 | #ioError(...) |       | 1 | #ioError(...)        |
| 2 | c.cfg |    | 2 | c.cfg's bytes |       | 2 | #syntaxError(pos: 3) |
+---+-------+    +---+---------------+       +---+----------------------+

good              bad
+---+--------+    +---+----------------------+
| i | value  |    | i | value                |
+===+========+    +===+======================+
| 0 | Config |    | 1 | #ioError(...)        |
+---+--------+    | 2 | #syntaxError(pos: 3) |
                  +---+----------------------+
```

`.map` replaces each value and keeps its key, `.where` keeps the entries that pass a test, and `read` reads a file through a port. A file that fails to read or parse doesn't stop the others. Each failure stays under its file's key, next to the successes, so you can split them, count them or report them. The read puts details such as the path in the failure's own fields (`#ioError(op:, path:, why:)`), so you don't have to thread that information through by hand.

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

```text
input: amounts = 3, #ioError(...), 4
sum1 = 7
sum2 = 7
sum3 = #ioError(...)

input: amounts = 3, 5, 4
sum1 = sum2 = sum3 = 12
```

## Collections

Zed's most fundamental structured data abstraction is the multi-level map: a map whose values can themselves be maps, to any depth. A table of sales by region and product is `region -> sku -> amount`, and `sales[r][s]` follows one *keypath*, the chain of keys that leads to one value. One rule holds everywhere: a keypath leads to exactly one value. Arrays, tables, groups and query results are all this one structure, so instead of a separate API for each container you learn a small set of operations that add, move, drop or reduce levels.

### Everything is a map

Arrays, sets, structs and functions are all maps from keys to values, and you write them and read them in the same way.

**Syntax:** `[a, b, c]`, `{ k -> v }`, `{ a, b }`, `m[k]`

```zed
xs = [3, 1, 4, 1, 5];                  // int[0..<5] -> int: keys from 0 up to but not including 5
ages = { "Ann" -> 36, "Bob" -> 41 };   // exact keys {"Ann", "Bob"}, int values
tags = { #red, #green };               // a set: a map from each member to itself

first = xs[0];                         // 3: the index is known to be in range
ann = ages["Ann"];                     // 36: the key is known to be there
// carol = ages["Carol"];              // ✗ rejected: this key can't be there
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

```text
tens           big           sorted
+---+----+     +---+----+    +------+----+
| i | x  |     | i | x  |    | rank | x  |
+===+====+     +===+====+    +======+====+
| 0 | 30 |     | 0 | 30 |    | 0    | 50 |
| 1 | 10 |     | 2 | 40 |    | 1    | 40 |
| 2 | 40 |     | 4 | 50 |    | 2    | 30 |
| 3 | 10 |     +---+----+    | 3    | 10 |
| 4 | 50 |                   | 4    | 10 |
+---+----+                   +------+----+
```

An array is a map whose keys are `0..<n`, a set is a map from each key to itself, a struct is a map from field names to values, and a function is a map too. So `xs[i]`, `f(x)` and `p.x` are all lookups, and the same operations work on all of them, except that an operation that visits every key needs a finite set of keys: a function over all of `int` can be called, but `group` or `==` on it is rejected. `K -> V` has a value at every key of `K`, while `K ->? V` may lack some keys, so a lookup can give `#notFound`. Nested maps are the normal way to hold tables: `Region -> Product -> rat` is a table of sales by region and product, stored in whichever layout suits the code that reads it. Your code never names the layout, so the compiler may pick a different one without your code changing.

### Grouping

`group` buckets the entries of a map by a key you compute, and `rekey` replaces the key.

**Syntax:** `m.group(x -> key)`, `m.rekey(x -> key)`

```zed
// users : UserId -> User
byCity = users.group(u -> u.city);      // City ->? (UserId -> User)
// byId = users.rekey(u -> u.id);       // ✗ rejected unless id is known to be unique
```

With three sample users, `group` adds the `city` level above the keys that were already there:

```text
input: users          byCity
+----+-----------+    +------+----+-----------+
| id | user      |    | city | id | user      |
+====+===========+    +======+====+===========+
| 1  | Ann, Oslo |    | Lima | 2  | Bob, Lima |
| 2  | Bob, Lima |    +------+----+-----------+
| 3  | Cid, Oslo |    | Oslo | 1  | Ann, Oslo |
+----+-----------+    |      | 3  | Cid, Oslo |
                      +------+----+-----------+
```

`group` adds a level, so nothing can be lost. The inner map keeps the users' original keys, exactly those of that city's users, which is why the inner arrow is `->`. Only cities with users occur, and each group is nonempty. Where SQL's `GROUP BY` must aggregate right away, a group here is just a level of the map, which you can reduce, read or reshape later. Since `rekey` can make two entries land on one key, the compiler demands evidence that the new key is unique, such as a function it can see never collides. If it can't see that, the error names the key expression and the evidence that would make it legal. A claim it can't prove, such as `@injective` (this function never gives two inputs one output) or a database's unique constraint, is checked at run time instead, and the result type gains `#collision`. When two entries really do collide, it shows both. No value ever silently overwrites another in Zed.

### Remapping

A remap states the shape a map has and the shape you want, and the compiler does the moving.

**Syntax:** `m as (pattern) into (pattern)`

```zed
transposed = matrix as (r -> c -> v) into (c -> r -> v);
ranking = scores as (name -> s) into (desc s -> name -> s);

// totals = sales as (region -> sku -> amount) into (region -> amount);   // ✗ rejected
totals = sales as (region -> sku -> amount) into (region -> sku >< (+) -> amount);
```

On small sample tables, with `rank` the level that `desc s` adds:

```text
input: matrix     transposed
+---+---+---+     +---+---+---+
| r | c | v |     | c | r | v |
+===+===+===+     +===+===+===+
| 0 | 0 | 1 |     | 0 | 0 | 1 |
|   | 1 | 2 |     |   | 1 | 4 |
|   | 2 | 3 |     +---+---+---+
+---+---+---+     | 1 | 0 | 2 |
| 1 | 0 | 4 |     |   | 1 | 5 |
|   | 1 | 5 |     +---+---+---+
|   | 2 | 6 |     | 2 | 0 | 3 |
+---+---+---+     |   | 1 | 6 |
                  +---+---+---+

input: scores     ranking
+------+----+     +------+------+----+
| name | s  |     | rank | name | s  |
+======+====+     +======+======+====+
| Ann  | 90 |     | 0    | Ann  | 90 |
| Bob  | 70 |     |      | Cid  | 90 |
| Cid  | 90 |     +------+------+----+
+------+----+     | 1    | Bob  | 70 |
                  +------+------+----+

input: sales                 totals
+--------+-----+--------+    +--------+--------+
| region | sku | amount |    | region | amount |
+========+=====+========+    +========+========+
| East   | A1  | 5      |    | East   | 8      |
|        | B2  | 3      |    | West   | 2      |
+--------+-----+--------+    +--------+--------+
| West   | A1  | 2      |
+--------+-----+--------+
```

In `transposed`, a value at row `r` and column `c` moves to row `c` and column `r`. A remap is another way of writing what `group`, `rekey` and `sort` do, and both forms compile to the same thing. In the `ranking` line, putting `desc s` in key position sorts by score, and keeping `name` as a level below it means that two people with the same score can't collide. A remap can move keys around, add levels or drop whole entries, but it can't overwrite a value. If you ask it to, as in the rejected `totals` line, you get an error that lists the ways out, and the last `totals` line is one of them. A shortened version of the error:

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

// bad = revenue as (region -> year -> sku -> amount) into (sku -> year -> amount);   // ✗ rejected
```

Each row is one keypath and its value. `bySku` has the same four values as `revenue`, reached by new keypaths. `perYear` first moves the levels, then collapses `region`, and `years` keeps only the keys:

```text
input: revenue                        bySku
+--------+------+-----+--------+      +-----+--------+------+--------+
| region | year | sku | amount |      | sku | region | year | amount |
+========+======+=====+========+      +=====+========+======+========+
| East   | 2024 | A1  | 5      |      | A1  | East   | 2024 | 5      |
|        |      | B2  | 3      |      |     |        | 2025 | 4      |
|        +------+-----+--------+      |     +--------+------+--------+
|        | 2025 | A1  | 4      |      |     | West   | 2025 | 2      |
+--------+------+-----+--------+      +-----+--------+------+--------+
| West   | 2025 | A1  | 2      |      | B2  | East   | 2024 | 3      |
+--------+------+-----+--------+      +-----+--------+------+--------+

levels moved, not yet reduced         perYear               years
+-----+------+--------+--------+      +-----+------+--------+   +--------+------+
| sku | year | region | amount |      | sku | year | amount |   | region | year |
+=====+======+========+========+      +=====+======+========+   +========+======+
| A1  | 2024 | East   | 5      |      | A1  | 2024 | 5      |   | East   | 2024 |
|     +------+--------+--------+      |     | 2025 | 6      |   |        | 2025 |
|     | 2025 | East   | 4      |      +-----+------+--------+   +--------+------+
|     |      | West   | 2      |      | B2  | 2024 | 3      |   | West   | 2025 |
+-----+------+--------+--------+      +-----+------+--------+   +--------+------+
| B2  | 2024 | East   | 3      |
+-----+------+--------+--------+
```

The constraint on every remap is this: no two values may end up at the same keypath through the map. The rejected `bad` line breaks it, because `(A1, 2025)` would have to hold both 4 and 2. The compiler judges this from the pattern and not from the data, so it rejects a dropped level even for an input that happens to have one entry under each key. What that leaves is:

- **Moving levels**, or packing them into a tuple key, as in `into ((sku, year) -> region -> amount)`. Each value keeps a keypath of its own.
- **Changing a key** in a way the compiler can see is one-to-one, as `k + 1` is, or **adding to a key**, as `desc s` does above, since the old key can still be recovered.
- **Dropping a level along with everything under it**, as `years` does. Nothing merges, because no value survives. This is the only way to drop a level without saying how to merge.
- **Collapsing a level with `><`**, as `perYear` does, which is the one way to merge values.

The rule exists because the alternatives are bad. A dictionary built in a loop quietly keeps the last value written to a key, and a database raises a duplicate-key error while the program runs. Here it's a compile error, and any merge is visible in the text. It also helps performance: since each value has a place of its own, threads can write results without locks, and merge code is needed only at a `><`. And a rejected remap tells you something about your data: the key you tried to drop is what told those values apart.

### Reducing

A reduction merges the values of one level into one value, using an operator you name.

**Syntax:** `m >< op`, `m >< op else fallback`, `(pattern >< op -> value)`, `m.foldl(init, op)`

```zed
total = readings >< (+);
longest = words.map(w -> w.len) >< max else 0;
pivot = sales as (i -> s) into (s.region -> s.product -> i >< (+) -> s.amount);
```

On small sample data:

```text
input: readings     total
+---+-------+       +-------+
| i | value |       | total |
+===+=======+       +=======+
| 0 | 2     |       | 10    |
| 1 | 5     |       +-------+
| 2 | 3     |
+---+-------+

input: words     .map(w -> w.len)          longest
+---+-----+      +---+-----+               +---------+
| i | w   |      | i | len |               | longest |
+===+=====+      +===+=====+               +=========+
| 0 | to  |      | 0 | 2   |               | 3       |
| 1 | be  |      | 1 | 2   |               +---------+
| 2 | not |      | 2 | 3   |
+---+-----+      +---+-----+

input: sales            levels moved, not yet reduced    pivot
+---+--------------+    +--------+---------+---+---+     +--------+---------+--------+
| i | sale         |    | region | product | i | s |     | region | product | amount |
+===+==============+    +========+=========+===+===+     +========+=========+========+
| 0 | East, pen, 5 |    | East   | ink     | 2 | 3 |     | East   | ink     | 3      |
| 1 | West, pen, 2 |    |        +---------+---+---+     |        | pen     | 9      |
| 2 | East, ink, 3 |    |        | pen     | 0 | 5 |     +--------+---------+--------+
| 3 | East, pen, 4 |    |        |         | 3 | 4 |     | West   | pen     | 2      |
+---+--------------+    +--------+---------+---+---+     +--------+---------+--------+
                        | West   | pen     | 1 | 2 |
                        +--------+---------+---+---+
```

The `pivot` line builds a table of sales by region and product. `i >< (+)` collapses the level `i`, adding the amounts that land on the same region and product.

Merging is always written out, with `><` or a named form such as `.sum`, `.count` or `foldl`. `><` runs in parallel, so except on floating-point values, which have their own rule below, it needs an operator that is safe to regroup: `+` and `max` are known to be, and for your own operators you state the law, as `@associative` (the grouping doesn't matter) and `@commutative` (the order doesn't matter) do below. The algebra decides how the reduction may run, so the same line can be a plain loop on one core or a tree across all of them.

```zed
struct Moments { n: int, sum: rat }

@associative @commutative
combine(positional a: Moments, positional b: Moments) =
  Moments(n: a.n + b.n, sum: a.sum + b.sum);

// values : [rat]
m = values.map(x -> Moments(n: 1, sum: x)) >< combine else Moments(n: 0, sum: 0r);
```

With three values:

```text
input: values     .map(x -> Moments(n: 1, sum: x))
+---+----+        +---+------------------------+
| i | x  |        | i | value                  |
+===+====+        +===+========================+
| 0 | 1r |        | 0 | Moments(n: 1, sum: 1r) |
| 1 | 2r |        | 1 | Moments(n: 1, sum: 2r) |
| 2 | 3r |        | 2 | Moments(n: 1, sum: 3r) |
+---+----+        +---+------------------------+

m
+------------------------+
| m                      |
+========================+
| Moments(n: 3, sum: 6r) |
+------------------------+
```

For `combine`, the compiler derives both laws from `+` on the fields. In general, a proved law lets the compiler regroup freely, while a claim that was only tested permits one fixed grouping and can still be wrong, and the report says which you have. If an operator isn't associative, use `foldl` or `foldr` to say which way to fold. A reduction over nothing can't be silently wrong: the `else` gives the answer for an empty collection, and without it the result type includes `#empty`, unless the operator has an identity or the collection is known not to be empty.

Floating-point sums get special care. `samples >< (+)` computes the exact sum and rounds it once, so the result doesn't depend on how the work was split or how many cores ran it. If you'd rather have speed than that guarantee, you ask for it, and it shows in the type: `samples >< (+) unordered`. Your own floating-point operator needs no law: with none, the reduction runs on one fixed grouping over the collection's order, so it gives the same bits at any core count.

### Pushing into a map

A map can be filled by pushing values to its keys, where a reducer says how values at one key merge.

**Syntax:** `name: K ->? V with reducer(op)`, `name[k] <- v`

```zed
hist: int ->? int with reducer((+));
for w in words { hist[w.len] <- 1; };

same = words.group(w -> w.len).count;   // the same table, written as a pull
```

With four words, `hist` gets one push per word, and `same` reaches the same table through a group:

```text
input: words     the pushes          hist
+---+-----+      +---+-----------+   +-----+---+
| i | w   |      | i | push      |   | len | n |
+===+=====+      +===+===========+   +=====+===+
| 0 | a   |      | 0 | [1] <- 1  |   | 1   | 1 |
| 1 | to  |      | 1 | [2] <- 1  |   | 2   | 2 |
| 2 | be  |      | 2 | [2] <- 1  |   | 3   | 1 |
| 3 | not |      | 3 | [3] <- 1  |   +-----+---+
+---+-----+      +---+-----------+

.group(w -> w.len)          same
+-----+---+-----+           +-----+---+
| len | i | w   |           | len | n |
+=====+===+=====+           +=====+===+
| 1   | 0 | a   |           | 1   | 1 |
+-----+---+-----+           | 2   | 2 |
| 2   | 1 | to  |           | 3   | 1 |
|     | 2 | be  |           +-----+---+
+-----+---+-----+
| 3   | 3 | not |
+-----+---+-----+
```

Sometimes it's clearer to say where each value goes (a push) than where each value comes from (a pull). `hist` can take pushes from many places, and `reducer((+))` adds up the values that land on one key. Because a push only contributes a value and never reads or overwrites one, parallel code can push with no locks. Without the reducer, the compiler has to prove that no two pushes land on one key, and otherwise rejects the program. Pushing and pulling compile to the same thing, so writing it this way doesn't choose the direction the data moves at run time. The compiler picks that for each edge of the graph.

### Joins

A join combines two maps on a shared field, either with a word such as `join` or with a `for` over both.

**Syntax:** `a.join(b, on: #field, kind: #left)`, `a.diff(b, on: #field)`, `for x in a, y in b where ...`

```zed
// Both inputs are uniquely keyed by OrderId; orderId is their join key.
paid = orders.join(payments, on: #orderId, kind: #left);
// OrderId -> (Order, Payment | #none)

unpaid = orders.diff(payments, on: #orderId);

shipped = for o in orders, s in shipments where o.orderId == s.orderId { (o, s) };
pairs = for i in 0..<n, j in i+1..<n { (i, j) };
```

On small sample data, where `o1` stands for the order with key 1, and `p1` and `s10` likewise:

```text
input: orders          input: payments
+---------+-------+    +---------+---------+
| orderId | order |    | orderId | payment |
+=========+=======+    +=========+=========+
| 1       | o1    |    | 1       | p1      |
| 2       | o2    |    | 3       | p3      |
| 3       | o3    |    +---------+---------+
+---------+-------+

paid                         unpaid
+---------+-------------+    +---------+-------+
| orderId | value       |    | orderId | order |
+=========+=============+    +=========+=======+
| 1       | (o1, p1)    |    | 2       | o2    |
| 2       | (o2, #none) |    +---------+-------+
| 3       | (o3, p3)    |
+---------+-------------+

input: shipments                 shipped
+------------+--------------+    +-----------------------+-----------+
| shipmentId | shipment     |    | (orderId, shipmentId) | value     |
+============+==============+    +=======================+===========+
| 10         | s10, order 1 |    | (1, 10)               | (o1, s10) |
| 11         | s11, order 1 |    | (1, 11)               | (o1, s11) |
| 12         | s12, order 3 |    | (3, 12)               | (o3, s12) |
+------------+--------------+    +-----------------------+-----------+

input: n = 3
pairs
+--------+--------+
| (i, j) | value  |
+========+========+
| (0, 1) | (0, 1) |
| (0, 2) | (0, 2) |
| (1, 2) | (1, 2) |
+--------+--------+
```

A `for` builds a map with one entry per combination that passes `where`. `on:` names the shared field with an atom, `kind: #left` keeps every entry of the left input, and `diff` keeps the left entries that have no match. A missing match in a left join is the atom `#none`, which the type shows, and not a row of nulls. For a `for` over several collections, the compiler can pick a hash join or a merge join, two standard ways to avoid comparing every pair, instead of two nested loops. Queries and loops compile to the same internal form, so they are optimized together.

A map doesn't say where it lives, so this code is the same whether `orders` is in memory, in a file (`with store(file(path, format))`) or in a database (`with store(postgres(...))`). You add that `with store(...)` annotation on the declaration and the join doesn't change, except that a stored map's type gains the failure its store can give, which you have to handle. A map that one function produces and another consumes may never be allocated at all. Where the consumer reads the values in order, each value passes straight to it as soon as it's computed, much as with `yield` in a generator or with a Unix pipe, and Zed needs no `yield` keyword to get this. Memory is needed where values really must be held: for a sort, an index built for lookups, a reduction's result, a value with several readers that can't share one pass, and a port or stored map.

Those choices follow from two goals of the language: you shouldn't have to write memory allocation at all, so the compiler is free to decide how to allocate optimally, and allocation should disappear wherever it can. That's why `orders` is declared as a map and not as an array, a list or a hash table.

### Chunks

`chunkBy` cuts an ordered collection into runs that share a key.

**Syntax:** `m.chunkBy(x -> key)`

```zed
sessions = clicks.chunkBy(c -> c.userId).map(s -> Session(start: s.first.time, count: s.count));
```

With four clicks in time order, `ann`'s clicks at `i` = 1 and `i` = 3 land in different chunks because `bob` clicked between them:

```text
input: clicks        .chunkBy(c -> c.userId)
+---+-----------+    +-----+---+-----------+
| i | click     |    | run | i | click     |
+===+===========+    +=====+===+===========+
| 0 | ann, t=10 |    | 0   | 0 | ann, t=10 |
| 1 | ann, t=12 |    |     | 1 | ann, t=12 |
| 2 | bob, t=15 |    +-----+---+-----------+
| 3 | ann, t=20 |    | 1   | 2 | bob, t=15 |
+---+-----------+    +-----+---+-----------+
                     | 2   | 3 | ann, t=20 |
                     +-----+---+-----------+

sessions
+-----+------------------------------+
| run | session                      |
+=====+==============================+
| 0   | Session(start: 10, count: 2) |
| 1   | Session(start: 15, count: 1) |
| 2   | Session(start: 20, count: 1) |
+-----+------------------------------+
```

If you have ever split a list into runs by hand, you know the easy mistake is forgetting to flush the last group. Here that can't happen, because the last chunk is included. And since a chunk exists only because a click fell into it, `s.first` is exact, with no `#none` case to handle.

### Vectors and matrices

An array's type can state its size, so shape mismatches are compile-time errors, not run-time errors: Zed is designed to eliminate as many types of run-time error as possible.

**Syntax:** `[T; n]`, `[T; r, c]`, `s * v`, `a.matmul(b)`

```zed
scale(positional s: T, positional v: [T; n]) = s * v;     // result: [T; n]

a: [f64; 2, 3] = [[1.0, 2.0, 3.0], [4.0, 5.0, 6.0]];
b: [f64; 3, 2] = [[1.0, 0.0], [0.0, 1.0], [1.0, 1.0]];
c = a.matmul(b);                                          // [f64; 2, 2]
// d = a.matmul(a);                                       // ✗ rejected: 3 columns, 2 rows
```

```text
input: s = 2.0, v = [1.0, 2.0]
scale(2.0, [1.0, 2.0]) = [2.0, 4.0]
```

The product, drawn as a map of rows to columns to values:

```text
c
+---+---+------+
| r | k | v    |
+===+===+======+
| 0 | 0 | 4.0  |
|   | 1 | 5.0  |
+---+---+------+
| 1 | 0 | 10.0 |
|   | 1 | 11.0 |
+---+---+------+
```

`[T; n]` is an array of `n` values of type `T`, and `[T; r, c]` is a matrix of `r` rows and `c` columns. In NumPy or a C matrix library, a wrong shape shows up only when the line runs, possibly hours into a job, and here it stops the build. A name in a shape that isn't bound to an integer is a size variable of the signature, so `[T; n, n]` is a square matrix. Dimension checks are ordinary type checks. `*` scales a vector or matrix by a number. Between two vectors or matrices it is an error, because it could mean several products: you write `matmul`, `dot` or `cross`. `matmul` isn't built in: it's a one-line remap with a reduction, in the same style as the `pivot` above.

## Time and repetition

### Recurrences

A recurrence defines an array by an equation over earlier entries, plus its boundary values.

**Syntax:** `x[i] = f(x[i-1]) with x[-1] = start;`

```zed
running[i] = running[i-1] + xs[i] with running[-1] = 0;

d[i][j] = min(d[i-1][j] + 1, d[i][j-1] + 1, d[i-1][j-1] + cost(a[i], b[j]))
  with d[-1][j in -1..<b::len] = j + 1, d[i in 0..][-1] = i + 1;
```

With `xs` = 3, 1, 4, with `a` and `b` arrays of the code points of "ab" and "ac", and with a `cost` of 0 for equal characters and 1 otherwise, `d[1][1]` is the edit distance, 1. The last table shows `d` as a grid with its boundary values, which are read but aren't entries of the result:

```text
input: xs     running           d              d with its boundaries
+---+---+     +---+---+         +---+---+---+
| i | x |     | i | v |         | i | j | v |       j = -1   0   1
+===+===+     +===+===+         +===+===+===+  i = -1     0   1   2
| 0 | 3 |     | 0 | 3 |         | 0 | 0 | 0 |  i =  0     1   0   1
| 1 | 1 |     | 1 | 4 |         |   | 1 | 1 |  i =  1     2   1   1
| 2 | 4 |     | 2 | 8 |         +---+---+---+
+---+---+     +---+---+         | 1 | 0 | 1 |
                                |   | 1 | 1 |
                                +---+---+---+
```

The code reads as it would on a whiteboard. The first line is a running total. The second is edit distance, the fewest single-character changes that turn one string into another, and it needs no explicit table and no choice of memoization (keeping each result for reuse) or fill order. The `with` clauses give the edges of the table: `d[-1][j]` is `j + 1` and `d[i][-1]` is `i + 1` for every `i` from 0 up, the costs against an empty string. The compiler reads the dependencies and picks a plan: it fills the table across your cores in dependency order if you need most of it, and memoizes on demand if you only touch part of it. In most languages, moving between those two plans means rewriting the code.

The compiler also recognizes some loops that look serial and runs them in parallel. An equation states only what each entry depends on, so nothing ties it to the order a written loop would fix:

```zed
cur[i] = max(xs[i], cur[i-1] + xs[i]) with cur[-1] = 0;
best = cur >< max else 0;

state[i] = csvStep(state[i-1], text::codepoints[i]) with state[-1] = #outsideQuotes;
```

With `xs` = 2, -3, 4, -1, 2, `best` is 5. For the text `a"b"`, if `csvStep` switches state at each quote character:

```text
input: xs     cur           state
+---+----+    +---+----+    +---+------+----------------+
| i | x  |    | i | v  |    | i | char | state          |
+===+====+    +===+====+    +===+======+================+
| 0 | 2  |    | 0 | 2  |    | 0 | a    | #outsideQuotes |
| 1 | -3 |    | 1 | -1 |    | 1 | "    | #insideQuotes  |
| 2 | 4  |    | 2 | 4  |    | 2 | b    | #insideQuotes  |
| 3 | -1 |    | 3 | 3  |    | 3 | "    | #outsideQuotes |
| 4 | 2  |    | 4 | 5  |    +---+------+----------------+
+---+----+    +---+----+
```

The first recurrence is maximum subarray, the largest sum of neighboring entries. The compiler recognizes that its step composes in any grouping, so it runs as a parallel scan, which computes all the running results across many cores. The second walks a CSV file with a small state machine. Because the states are finite, the compiler can tabulate the transitions, and tables compose in any grouping, so a job usually done one character at a time splits across cores.

### Loops

A loop describes one step, and the loop as a whole is a value holding the final state and the history.

**Syntax:** `loop { x' = f(x) with x = start; until done; }`, `loop t { while c; ... }`, `run.x`, `run::frames`

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

```text
sim::frames
+---+-------+-------+
| t | pos.x | vel.x |
+===+=======+=======+
| 0 | 1     | 2     |
| 1 | 3     | 3     |
+---+-------+-------+
```

`pos'` is the next value of `pos`, written in terms of the current values. `with pos = p0` gives its value before the first step, and `until` is tested after each step. Both updates here read the old `pos`, so they don't race and their order doesn't matter. Each step writes each variable once, so a data race can't be written. Every read in a step sees the same snapshot of the previous step, so you need no temporary variables to keep a simultaneous update straight. After the loop, `sim.pos` is the final value.

`sim::frames` is every step of the run, kept only if you read it. If you don't, the compiler keeps only the steps the loop still reads, so you never choose between a ring buffer and a full log by hand. Reading it is how you write undo:

```zed
run = loop t {
  while t < edits::len;
  doc' = doc.patch(edits[t]) with doc = empty;
};

previous = run::frames[run::len - 2]?.doc else empty;
```

`loop t` names the step counter `t`, and `while` is tested before each step. With two edits `e1` and `e2`, and with `empty` the empty document:

```text
input: edits     run::frames
+---+------+     +---+-----------------+
| t | edit |     | t | doc             |
+===+======+     +===+=================+
| 0 | e1   |     | 0 | empty.patch(e1) |
| 1 | e2   |     | 1 | that.patch(e2)  |
+---+------+     +---+-----------------+
```

`previous` is the document after `e1`. With no edits, or just one, the lookup finds no frame and `previous` is `empty`.

`patch` applies one edit to the document. The versions share structure, so keeping them all doesn't copy the document each time, although the history still uses memory.

### Methods and the next value

A method is a function on a struct, and it can define the struct's next version with the same `'` that a loop uses.

**Syntax:** `Type.method() { field' = ...; }`, `x.method()`, `x*.method()`

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

Here `n'` is the value of `n` in the next version of this struct. The method doesn't change `start`: it returns a new `Counter` and its declared result, and you have to take both. In a loop body, a `*` makes a call look like mutation: `prev = c*.bump(3);` replaces `c` in the loop's next step. So no call changes a value you hold unless the text shows a `*`, which makes state changes easy to find by reading and leaves the compiler free to treat every other call as pure, which means it has no side effects.

### Only what's needed runs

A value no result depends on doesn't have to be computed, so unused fields and unbounded ranges cost nothing extra.

**Syntax:** `for i in n.. { ... }`, unused fields, `.first`

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

```text
stats([1.0, 2.0, 3.0]): n = 3.0, mean = 6.0 / 3.0 = 2.0
m = 2.0, and sd has not run

for i in 2.. = 2, 3, 4, 5, ...
.where(isPrime) = 2, 3, 5, ...
firstPrime = 2
```

`{ mean:, sd: }` is a record whose fields take their values from the names `mean` and `sd`. A caller that reads `.mean` doesn't pay for `sd`, and you don't need two versions of the function or a flag. Zed isn't lazy in the Haskell sense, where a value is computed when first read: any evaluation order that gives the same value is legal, and the compiler chooses by cost. The `firstPrime` search runs over an unbounded range. The compiler may try candidates in parallel, and once a prime is found and every smaller candidate has been ruled out, the larger ones can be canceled.

## The outside world

### Ports

Ports are declared channels to the outside world, and they are the only way a program reaches it.

**Syntax:** `main(input: T) -> (output: U) { output <- value; }`

```zed
main(req: Stream(Query)) -> (resp: Stream(Answer)) {
  resp <- req.map(q -> answer(q));
}
```

```text
input: req delivers q1, then q2
resp carries answer(q1), then answer(q2)
```

A `Stream` is a sequence of values that arrive over time. Ports are declared in `main`'s header or as stored collections, which are maps declared `with store(...)`: files, sockets, clocks, devices, databases and the like. Foreign calls and logging go through ports too. Everything else is a pure value, so Zed needs no effect system (type annotations that record side effects). It also means the compiler can reorder, parallelize or skip anything that isn't a port operation, since nothing else can be observed. Reading a port gives you a value, and `<-` pushes one out. So a server, a batch job and a pipeline are all the same kind of thing: a function from input ports to output ports.

Runs repeat exactly, apart from a short list such as the order that messages arrive at a port and running out of a resource. Inputs and arrival order can be recorded, so you can replay a failing run in a test.

### Timeouts and retries

A port's reliability settings are declared on the port, and the ones that can fail show up in its type.

**Syntax:** `with timeout(d)`, `with retry(n, backoff: b)`, `with bound(n, overflow: policy)`

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

`kv` is a key-value store, `[u8]` is an array of bytes, `0.2r with units("s")` is 0.2 seconds, and `#fixed(d)` waits up to `d` between attempts. With this `timeout`, a read of `cache` is `[u8] | #ioError | #timeout | #notFound`, and the program has to deal with that, here by treating anything other than a hit as a miss. In most languages a timeout is an exception nothing forces you to catch. `retry` adds no failure member, and the timeout covers all the attempts together. Pure code never times out, because a computation's finishing time isn't a value.

Retries, hedged requests (a second copy of a slow request), circuit breakers (refusing calls for a while after repeated failures), rate limits and failover (switching to a replacement server) are declared on the port in the same way, so the policy sits in one place and not in wrapper code around each call. The compiler permits retries only for operations that are safe to repeat, so a write that may already have landed needs a guarantee that doing it twice has the effect of doing it once (idempotence) before it can be retried. Queues declare what happens when they are full (`#block`, `#dropOldest` or `#full`), so every queue has a limit, and by default a writer waits when it is full.

### Databases

A database table is declared as a map on a store, and its schema is checked at build time.

**Syntax:** `name: K ->? V with store(...)`

```zed
orders: OrderId ->? { total: rat, note: Utf8String | #none }
  with store(postgres(dbUrl, table: "orders", schema: sql("db/orders.sql")));

n = orders[id]?.note;     // Utf8String | #none | #notFound | #dbError
```

```text
input: orders              n, for each id
+----+-------+--------+    +----+-----------+
| id | total | note   |    | id | n         |
+====+=======+========+    +====+===========+
| 1  | 9r    | "gift" |    | 1  | "gift"    |
| 2  | 4r    | NULL   |    | 2  | #none     |
+----+-------+--------+    | 3  | #notFound |
                           +----+-----------+
```

If the database can't answer, `n` is `#dbError` for any `id`.

You read a stored table with the same `[key]` as any other map, and the same `where` that is a loop over a map in memory may run as a SQL `WHERE` clause here. The schema check compares your declaration with the SQL schema and needs no live connection: a column that allows NULL read as non-optional, or an unbounded string written to a `varchar(80)`, is a compile error at this line, where elsewhere it would fail a request in production. At startup, the program compares the columns it uses with the real database. On a port that supports transactions, such as Postgres, writes made in one step of the program form one transaction, and you never write `begin` or `commit`.

### Incremental updates

When an input changes, the compiler can update the affected results or recompute them in full, and `@memoized` asserts that a value is kept for reuse.

**Syntax:** `@memoized`

```zed
// sales is keyed by SaleId; each sale has a region and an amount.
@memoized
report = sales
  .group(s -> s.region)
  .map(rows -> rows.map(s -> s.amount).sum);
```

Here are three sales, shown as region and amount. If sale 7 then changes from 5 to 6, East's total becomes 9 and West's stays 2:

```text
input: sales            .group(s -> s.region)            report
+--------+---------+    +--------+--------+---------+    +--------+-----+
| saleId | sale    |    | region | saleId | sale    |    | region | sum |
+========+=========+    +========+========+=========+    +========+=====+
| 7      | East, 5 |    | East   | 7      | East, 5 |    | East   | 8   |
| 8      | West, 2 |    |        | 9      | East, 3 |    | West   | 2   |
| 9      | East, 3 |    +--------+--------+---------+    +--------+-----+
+--------+---------+    | West   | 8      | West, 2 |
                        +--------+--------+---------+
```

Inside the `.map`, East's `rows.map(s -> s.amount)` is `{ 7 -> 5, 9 -> 3 }`, whose `.sum` is 8.

Incremental updates need no annotation. `@memoized` makes the build fail if this value isn't kept for reuse. When an input changes, the change goes through the same graph as a new batch of values (a *wave*), and only what it affects is recomputed, unless a full recomputation would cost less. Changing one sale's amount updates its region's total, and moving a sale to another region updates both. The update stops wherever nothing downstream can see a difference. Spreadsheets, build systems and reactive user interfaces each build this by hand. In Zed the compiler does it, and an incremental result always equals what a full recomputation would give.

This also powers live editing: a change to your source code is one more wave on one more port, so a running program can pick up the edit without a restart. By default the edited program reruns on the recorded inputs, so no extra code is needed. A run whose input history isn't kept, such as a server's, continues from its current loop values instead, and an edit that changes the type of a loop variable, or renames or removes one, must supply a migration, code that converts the old values.

## Checks at compile time

### Ranges and refinements

A type can state a range or a condition on its values.

**Syntax:** `int[lo..=hi]`, `x.refine(p)`, `@ensure`

```zed
struct Span { lo: int, hi: int[lo..] }

width(positional s: Span) = s.hi - s.lo;   // inferred: int[0..]
// bad = Span(lo: 3, hi: 1);               // ✗ rejected: hi must be at least lo

@ensure odd(positional x) = (x * 2 + 1).refine(v -> v < 100);
                                           // inferred: x <= 49
a = odd(12);
// b = odd(60);                            // ✗ rejected: 60 > 49
```

```text
input: s = Span(lo: 1, hi: 4)
width(s) = 3, a = 25
```

The compiler tracks ranges, and relations between fields, through arithmetic without any annotations from you. That is how it removes bounds checks and picks the smallest machine representation. `refine` checks a condition, at run time unless the compiler can settle it first, and gives `#invalid` if it fails. `@ensure` forbids a run-time check: the compiler has to push the condition back onto the inputs and reject the program if it can't prove them safe, so the check moves to compile time.

A field's range may name another field. The compiler reasons about such bounds with linear arithmetic (sums of variables times constants), and no SMT solver, a general theorem prover, is involved. The checks come from a small set of procedures that always finish, so the compile time is predictable and the error message says exactly what stopped the proof.

### Units and taint

Units and taint are labels you attach to a value with `with`.

**Syntax:** `with units("...")`, `with taint(#label)`

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

```text
input: input = "<b>"
d = 6.0 in m
page = render of "<p>&lt;b&gt;</p>", if escapeHtml escapes as usual
```

These are *facets*: extra facts about a value, tracked through every operation at compile time. Units and taint have no run-time cost. Units catch mistakes in formulas that a plain `f64` lets through. Taint follows untrusted input through your program. Here `render` declares that it takes only clean text and `escapeHtml` is the function that removes the taint, so passing user input straight through is a type error. Any program can define a facet of its own in the same way, such as a latency or a parity.

### Cost

Annotations turn performance requirements into build failures.

**Syntax:** `f::cost`, `@cost(b)`, `@fused`, `@noalloc`

```zed
@cost(xs::len)
@fused
sumSquares(positional xs: [f64]) = xs.map(x -> x * x) >< (+);

@cost(xs::len * log(xs::len))
ranked(positional xs: [int]) = xs.sort(desc x -> x);

@noalloc
lerp(positional a: f64, positional b: f64, positional t: f64) = a * (1.0 - t) + b * t;
```

```text
input: [1.0, 2.0, 3.0], [3, 1, 2], 0.0, 10.0, 0.5
sumSquares([1.0, 2.0, 3.0]) = 14.0
ranked([3, 1, 2])           = [3, 2, 1]
lerp(0.0, 10.0, 0.5)        = 5.0

These are the values. This page doesn't work out the bound that f::cost reads
for these functions, beyond what the @cost lines state.
```

Every function has a computed upper bound on its work (the total number of operations) and its parallel depth (the longest chain of operations that must run one after another), which you can read as `f::cost` and `f::depth`. Where no bound can be proved, they say `#unbounded`. Annotations like these are assertions about the plan the compiler chose: `@cost` states a bound, `@fused` says no intermediate collection is built, and `@noalloc` says the code uses no memory beyond registers. If one is false, the build fails, so a slowdown in a hot path shows up on the commit that caused it, and not later in production.

## Code that runs at build time

### Partial evaluation

An expression the program needs is computed at build time when its inputs are known then.

**Syntax:** none. It applies to any needed expression with known inputs.

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

```zed
type Size = #small | #medium | #large;

sizes = Size::values;       // {#large, #medium, #small}: atoms sort by name
names = User::fields;       // the fields of User, by name and type
```

```text
sizes = { #large, #medium, #small }
names = id, an int, and name, a Utf8String
```

Generic code uses these reads: that's how `Json.decode` knows what `User` looks like. Reflection has no run-time cost, which is why a generic decoder needs neither a code generator nor a slower reflective path.

### Grammars

A grammar describes a text or binary format.

**Syntax:** `struct Name grammar { ... }`, `type T = Utf8String matching grammar { ... }`, `T.parse(s)`, `x.serialize`

```zed
struct Vec3 grammar { "(" x: f64 "," y: f64 "," z: f64 ")" }

v = Vec3.parse("(1.0, 2.0, 3.0)") else Vec3(x: 0.0, y: 0.0, z: 0.0);
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

Binary formats work the same way, with the layout given by words such as `bits`, `endian` and `length`. This is the layout of a PNG chunk:

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
Chunk(n: 1, kind: the 4 bytes of "IDAT", data: the 1 byte 2A, crc: 7)
```

### Symbolic math

Programs can read a function, rewrite it and compile it again.

**Syntax:** `f::source`, `expand(e)`, `derivative(e)`

```zed
p = ((x: rat) -> (x + 1r) ** 2)::source;
e = expand(p);          // x ** 2 + 2r * x + 1r
d = derivative(p);      // 2r * x + 2r
```

```text
e = x ** 2 + 2r * x + 1r
d = 2r * x + 2r
```

The source of a function is a value, and rewriting it is an ordinary program, so algebra and differentiation are library code and not a separate tool. Each rewrite carries a proof that the compiler checks step by step, and the types of the function's parameters are the assumptions, so `(x * y) div y` simplifies to `x` when `y` is known to be at least 1, and not when `y` may be 0. `compile` turns the result back into a function.

## Tests, laws and proofs

### Tests next to the code

A `test` table lists inputs and expected outputs for a definition.

**Syntax:** `f(...) = ... test { input -> output, ... }`

```zed
double(positional x) = x * 2 test { 0 -> 0, 2 -> 4, -3 -> -6 }
```

```text
double(0), double(2), double(-3) = 0, 4, -6, which match the table
```

Tests live on the definition and run at build time, so they stay next to what they test, and since a table is data, a tool can read or generate it. A function whose domain the source lists member by member, such as `bool`, is run on every input, and `@exhaustive` asks for the same on any other finite domain, such as `int[1..=9]`.

### Laws

A `law` states a property of your code for the compiler to prove or test.

**Syntax:** `law name(x: T) = expression;`

```zed
law doubleIsSum(x: int) = double(x) == x + x;
law addComm(a: int, b: int) = a + b == b + a;
law sortTwice(xs: [int]) = xs.sort(asc x -> x).sort(asc x -> x) == xs.sort(asc x -> x);
```

```text
input: x = 3; a = 1, b = 2; xs = [3, 1, 2]
double(3) == 3 + 3      6 == 6
1 + 2 == 2 + 1          3 == 3
sorting [3, 1, 2] twice and once both give [1, 2, 3]

These are single cases. Which grade (how far the compiler got in checking a law)
the build reports for each of these three laws isn't worked out here, since it
depends on the compiler's rewrites.
```

A test checks the cases you thought of, and a law states what has to hold for every input. The compiler tries to prove a law with a fixed ladder of methods. For a domain whose members the source lists, such as `bool` or a set of atoms, it checks every case, and otherwise it tries the rewrites and automatic proof methods it has. If those fail, the law is tested on generated inputs. It then reports how far it got: exhaustively checked, proved, checked up to a bound, tested, assumed or unknown. An unproved law doesn't stop the build unless you ask it to with `@proved`, `@strict` or `--strict`.

The optimizer can use proved laws as rewrites. A `law` that was only tested is never used to rewrite your program. An `@associative` annotation that was only tested can still choose a fixed regrouping, and the report says so.

### Model checking

A loop that collects every reachable state, together with a law over those states, checks a state machine at build time.

**Syntax:** `loop` plus `law`

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

law neverBothGreen(ns: Signal, ew: Signal) = (Junction(ns: ns, ew: ew) in reachable.R).implies(ns == #red || ew == #red);
```

```text
reachable.R
+--------+--------+
| ns     | ew     |
+========+========+
| #green | #red   |
| #red   | #green |
| #red   | #red   |
+--------+--------+
```

The loop reaches these three states in one step, and the next step adds none. None has both lights green, so the law holds.

A loop is a state machine, so the set of states it can reach is a fixpoint (a value one more step doesn't change) you can write in a few lines, and for a finite state space the compiler computes it at build time. Here `.flatMap` gives each state a list of next states and joins the lists, `.image` collects a list's values into a set, `.union` combines two sets, `.implies` is logical implication, the loop stops when `R` stops growing, and `reachable.R` is the final set. A `Junction` with both lights green is a legal value, but no sequence of commands reaches it, and the law checks exactly that. This covers the safety checks you would use TLC, a widely used model checker, for, in the language the system is written in. Liveness (something good eventually happens) must be stated as a bound or a decreasing measure, and properties that rely on fairness (no ready action of the environment is put off forever) can't be expressed. A failed check reports the sequence of steps that reached the bad state, as a value you can replay.

## Under the hood

### Error messages

A compile error says what failed, why, and what would fix it.

**Syntax:** none.

Every error gives the rule that failed and the checker's whole chain of reasoning: each constraint, where it came from and how it reached this line. When the compiler has concrete evidence, such as two keys that collide or a value no `match` arm covers, it shows it. When a proof is missing, it names the expression or region it couldn't resolve. It then lists the repairs that would work, as in the [remap error](#remapping) above. The rules that reject a program are fixed lists, so whether a program is accepted never depends on how strong the optimizer is. The one exception is an assertion you write about the plan, such as `@cost` or `@fused`, which checks the plan the compiler chose.

### Calling C, and being called from C

Annotations declare C functions to call and Zed functions to expose to C.

**Syntax:** `@foreign("lib", "symbol")`, `@export("c", "symbol")`, `@stateless`

```zed
@foreign("m", "cbrt") @stateless cbrt: (positional x: f64) -> f64;

root = cbrt(8.0) else 0.0;

@export("c", "zed_score")
score(positional a: f64, positional b: f64) = a * 0.7 + b * 0.3;
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

Most intermediate collections are never allocated at all, as [Joins](#joins) explains, and this stop is about the rest. Zed has no garbage collector and no lifetimes, and ownership annotations appear only on foreign signatures. Zed values can't form cycles, so exact reference counting is enough, and the compiler removes most of it: where a last use is known statically, the free is simply placed there, with no count at all. A functional update of a value nothing else refers to happens in place. Cyclic data lives in arenas, blocks of memory whose nodes are freed together, or in id-indexed graphs, whose nodes refer to each other by key, so a stale lookup gives `#notFound` and not a dangling pointer. Freeing is spread out across the scheduler's work, so there are no garbage-collection pauses and no long chains of frees. `@noalloc` and `@preallocated` let you assert a bounded footprint and have the build fail if it doesn't hold.

### Parallelism and determinism

The compiler decides what runs in parallel, and the output doesn't change with the number of cores.

**Syntax:** none.

Any two parts of a program with no dependency between them may run at once, and the compiler splits the work using the dependency graph and the laws of each operator. Outputs are bit-identical at any core count, floating-point reductions included, so a test that passes on your laptop means the same on a 64-core server, and a bug seen there can be reproduced on one core. The exceptions are a short, enumerated list: arrival order at ports, the interleaving at an output port that declares one, foreign-call order the program leaves open, `unordered` reductions, and running out of a resource. There is no undefined behavior, except where a foreign library breaks a promise made about it.

### Targets

The same program compiles to several kinds of hardware and platform.

**Syntax:** none.

A program states dependencies and names no threads, addresses or machines, and that is what lets it move between targets. One intermediate representation (the form a compiler holds a program in) sits under everything. Back ends (the compiler stages that generate code) compile it to native multicore code through the MLIR and LLVM compiler toolkits, and to WebAssembly (portable code for browsers and other runtimes), GPUs, distributed dataflow (where the keys of your data double as partition keys), hardware synthesis (circuit designs) and microcontrollers. The compiler is written in Zed itself, on top of a small kernel, the core everything else is built on. A program that needs a port its target doesn't have is rejected at build time, and the error names the port and how the program reached it.

## License

Zed is released under the [MIT License](LICENSE).
