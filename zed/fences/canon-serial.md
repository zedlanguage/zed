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
