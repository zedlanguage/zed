| Part | Tag | Fields in order |
| Definition | — | `name: string, domain: option of domain, facets: list of facet, body: term` |
| Facet | — | `hint: byte, kind: string, value: value` |
| Domain | — | `pieces: list of piece, class: class` |
| Piece | — | `low: end, high: end` |
| Integer | — | `sign: byte, magnitude: magnitude` |
| Magnitude | — | `limbs: list of word` |
| Power | — | `prime: word, exponent: integer` |
| Entry | — | `key: value, value: value` |
| Arm | — | `pattern: pattern, body: term` |
| Field pattern | — | `field: string, pattern: pattern` |
| Evidence | — | `properties: list of property` |
| Property | — | `name: string, grade: grade` |
| End | Tag | Fields in order |
| Below every integer | 0 | — |
| Integer in i64 | 1 | `value: word` |
| Above every integer | 2 | — |
| Integer past i64 | 3 | `value: integer` |
| Class | Tag | Fields in order |
| No integer | 0 | — |
| Class in i64 | 1 | `modulus: word, residue: word` |
| Class past i64 | 2 | `modulus: integer, residue: integer` |
| Value | Tag | Fields in order |
| Boolean | 0 | `value: byte` |
| Integer | 1 | `value: word` |
| f64 | 2 | `bits: word` |
| String | 3 | `length: word, text: utf8` |
| Atom | 4 | `name: string, payload: list of value` |
| Tuple | 5 | `items: list of value` |
| Path | 6 | `items: list of value` |
| Family | 7 | `entries: list of entry` |
| Integer past i64 | 8 | `value: integer` |
| Rational | 9 | `sign: byte, numerator: magnitude, denominator: magnitude` |
| Atom with fields | 10 | `name: string, fields: list of string, payload: list of value` |
| Atom with empty payload | 11 | `name: string` |
| f32 | 12 | `bits: word` |
| Integer with powers | 13 | `sign: byte, numerator: magnitude, powers: list of power` |
| Rational with powers | 14 | `sign: byte, numerator: magnitude, denominator: magnitude, powers: list of power` |
| Pattern | Tag | Fields in order |
| Wildcard | 0 | — |
| Binder | 1 | — |
| Literal | 2 | `value: value` |
| Atom | 3 | `name: string, payload: list of pattern` |
| Tuple | 4 | `items: list of pattern` |
| Any atom | 5 | — |
| Atom with fields | 6 | `name: string, fields: list of field pattern` |
| Type test | 7 | `type: string` |
| Term | Tag | Fields in order |
| Literal | 1 | `value: value` |
| Bound variable | 2 | `level: word` |
| Definition | 3 | `address: address` |
| Free variable | 4 | `name: string` |
| Lambda | 5 | `parameters: word, body: term` |
| Application | 6 | `function: term, arguments: list of term` |
| Primitive | 7 | `code: word, arguments: list of term` |
| Primitive as a function | 8 | `code: word` |
| Let | 9 | `value: term, body: term` |
| If | 10 | `condition: term, then: term, else: term` |
| Match | 11 | `scrutinee: term, arms: list of arm` |
| fam | 12 | `domain: term, body: term` |
| reindex | 13 | `family: term, kf: term, vf: term, witness: witness` |
| discard | 14 | `family: term, sel: term` |
| fold | 15 | `family: term, op: term, identity: option of term, depth: word, ev: evidence` |
| fix | 16 | `init: term, step: term, kind: fix kind, ev: evidence` |
| gen | 17 | `init: term, step: term, guard: term, position: guard position` |
| Port read | 18 | `port: string` |
| Port push | 19 | `port: string, value: term` |
| Primitive | Code |
| `a + b` | 0 |
| `a - b` | 1 |
| `a * b` | 2 |
| `a / b` | 3 |
| `a div b` | 4 |
| `a mod b` | 5 |
| `-a` | 6 |
| `a == b` | 7 |
| `a != b` | 8 |
| `a < b` | 9 |
| `a <= b` | 10 |
| `a > b` | 11 |
| `a >= b` | 12 |
| `a && b` | 13 |
| `a \|\| b` | 14 |
| `!a` | 15 |
| `min` | 16 |
| `max` | 17 |
| `f[k]` on a family | 18 |
| `f.count` | 19 |
| `f.union(g)` | 20 |
| a key path built from its keys | 21 |
| the key at a given position of a key path | 22 |
| the number of keys of a key path | 23 |
| a tuple `(a, b, …)` | 24 |
| `t[i]` on a tuple | 25 |
| `a ++ b` on two strings | 26 |
| `a ^ b` | 27 |
| an atom built from its name, its field names and its payload | 28 |
| `String` | 29 |
| `int` | 30 |
| `rat` | 31 |
| `f64` | 32 |
| `abs` | 33 |
| `len` | 34 |
| `lower` | 35 |
| `upper` | 36 |
| `trim` | 37 |
| `sum` | 38 |
| `bitAnd` | 39 |
| `bitOr` | 40 |
| `bitXor` | 41 |
| `bitNot` | 42 |
| `shl` | 43 |
| `shr` | 44 |
| `popCount` | 45 |
| `leadingZeros` | 46 |
| `trailingZeros` | 47 |
| `rotl` | 48 |
| `rotr` | 49 |
| `f64Bits` | 50 |
| `codePoint` | 51 |
| `scalar` | 52 |
| `utf8` | 53 |
| `fromUtf8` | 54 |
| `mulHi` | 55 |
| `bitReverse` | 56 |
| `byteSwap` | 57 |
| `pdep` | 58 |
| `pext` | 59 |
| `funnelShl` | 60 |
| `funnelShr` | 61 |
| `f[k]` on a family whose keys are one integer interval, each present | 62 |
| `f32` | 63 |
| `sqrt` | 64 |
| `fma` | 65 |
| a family display `{k0 -> v0, k1 -> v1, …}` | 66 |
| `k in f` | 67 |
| `range` | 68 |
| the first entry of a level in key order | 69 |
| the last entry of a level in key order | 70 |
| the entry after a given one of a level in key order | 71 |
| the entry before a given one of a level in key order | 72 |
| `f.first` | 73 |
| `f.last` | 74 |
| `split` | 75 |
| `lines` | 76 |
| `concat` | 77 |
| `a ..`, the integers from `a` with no upper end | 78 |
| `a ++ b` on two lists | 79 |
| a function value with the parameter list of the function it holds | 80 |
| a call through a function value, placed by the function called | 81 |
| Witness | Tag | Fields in order |
| Residue | 0 | — |
| Catalog | 1 | `name: string` |
| Fix kind | Tag | Fields in order |
| Lattice | 0 | `join: term` |
| Definedness | 1 | — |
| Guard position | Tag | Fields in order |
| Before | 0 | — |
| After | 1 | — |
| Grade | Tag | Fields in order |
| Axiom | 0 | — |
| Checked exhaustive | 1 | — |
| Proved | 2 | — |
| Bounded | 3 | — |
| Obligated | 4 | — |
| Assumed | 5 | — |
