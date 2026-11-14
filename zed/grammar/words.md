<!-- The table of defined words of the spec's DESIGN.md (sec:grammar), each cell cut to its backquoted words, copied by the sync tool: do not edit. -->

| Layer | Annotations | Facet words (`with name(…)`) | Defined forms |
|---|---|---|---|
| L1 | — | — | `main`, `MainArgs`, `files`, `Never`, `U8String`, `Utf8String`, `Utf16String`, `Utf32String`, `Files`, `bitAnd`, `bitOr`, `bitXor`, `bitNot`, `shl`, `shr`, `popCount`, `leadingZeros`, `trailingZeros`, `rotl`, `rotr`, `f64Bits`, `f32Bits`, `f16Bits`, `bf16Bits`, `f16`, `bf16`, `mulHi`, `bitReverse`, `byteSwap`, `pdep`, `pext`, `funnelShl`, `funnelShr`, `char8`, `char16`, `char32`, `utf8`, `fromUtf8`, `CommandLine` |
| L2 | `@hash`, `@nonblocking` | — | `build` |
| L3 | — | — | `main::args`, `map`, `where`, `foldl`, `foldr`, `reduce`, `any`, `all`, `find`, `split`, `lines`, `concat`, `split`, `fam`, `discard`, `fold`, `reindex`, `gen` |
| L4 | — | — | `rekey`, `group`, `flatMap`, `tag`, `#collision` |
| L5 | — | — | `sort`, `orderedValues`, `scan`, `Seq`, `zip`, `patch`, `join`, `diff`, `first`, `last`, `minBy`, `maxBy`, `slice`, `take`, `drop`, `takeWhile`, `chunkBy`, `upTo`, `from`, `#assertEmpty` |
| L6 | — | — | `fix`, `.fold`, `::frames`, `Ast`, `Facet`, `Lattice`, `Reduction`, `Store`, `Rejection`, `Interval`, `Congruence`, `Bound` |
| L7 | `@foreign`, `@export`, `@borrowed`, `@stateless`, `@log`, `@after`, `@thread` | `commutes`, `reducer`, `bound`, `timeout`, `failure`, `order`, `finite`, `bits`, `endian`, `at`, `length`, `terminated`, `tagged`, `arg`, `release`, `keeps`, `consumes`, `transfer`, `held`, `notPassed`, `anyThread`, `handedBack`, `dropsHeld`, `concurrency`, `period`, `priority`, `coalesce`, `cancel`, `kill`, `limits`, `names` | `Stream`, `window`, `merge`, `latest`, `Instant`, `Duration`, `now`, `clock`, `randomBytes`, `spawn`, `run`, `Process`, `connect`, `listen`, `Ptr`, `#lost`, `i8`, `i16`, `i32`, `i64`, `i128`, `u8`, `u16`, `u32`, `u64`, `u128`, `log`, `::keypath`, `::bytes`, `via`, `then(…)`, `LossyCodec`, `DecodeFailure`, `#badEncoding`, `utf8Text`, `utf16Text`, `utf32Text`, `utf16Units`, `normalize`, `lines`, `rawLines`, `textLines`, `Line`, `RawLine`, `escaped`, `each`, `delimited`, `lengthPrefixed`, `fixedSize` |
| L10 | `@checked`, `@fpwarn`, `@fpsafe`, `@approx` | — | `refine`, `Codec`, `CanonicalCodec` |
| L11 | — | — | `f::ast`, `Ast`, `::source`, `::ast`, `::shape`, `::names`, `::fields`, `::members`, `::values`, `::name`, `FloatClass`, `Constraints`, `::constraints`, `::min`, `::max`, `::range`, `::residue`, `::minLen`, `::maxLen`, `meet`, `entails` |
| L12 | — | `units`, `countedIn`, `parity`, `latency`, `dist` | `UnitText`, `Nonzero`, `UnitName`, `UnitKind`, `UnitPower`, `UnitFactor`, `UnitProduct`, `::units`, `UnitDef`, `UnitSpelling`, `to(…)` |
| L13 | — | `taint` | — |
| L14 | — | `layout` | `complex`, `quat`, `oct`, `conj`, `normSq`, `inv`, `abs`, `csqrt`, `cexp`, `clog`, `cpow`, `matmul`, `dot`, `norm`, `cross`, `solve`, `#singular` |
| L15 | `@invariant`, `@ensure`, `@exhaustive`, `@exact` | — | `Proof`, `byInduction`, `bySimp`, `byCases`, `using`, `anyIntro`, `anyElim`, `allElim`, `allIntro`, `::grade`, `reflect` |
| L16 | `@associative`, `@commutative`, `@idempotent`, `@injective`, `@assume` | `unique` | — |
| L17 | `@measure`, `@total` | — | `total`, `zedc build --total` |
| L18 | `@cost`, `@equivalent`, `@fused`, `@memoized`, `@noalloc`, `@preallocated`, `@stack` | — | `preallocated`, `f::cost`, `f::depth`, `f::costWithMultipliers`, `f::depthWithMultipliers` |
| L19 | — | — | `compile`, `mix` |
| L20 | — | `bitorder` | `records`, `json`, `csv` |
| L21 | — | `store`, `retry`, `hedge`, `breaker`, `rate`, `peers` | `#unavailable` |
| L22 | `@decides` | — | `ofNat`, `Semigroup`, `Monoid`, `NonCommRing`, `CommRing`, `Ring`, `additive`, `dual`, `byStrongInduction`, `byCollectionInduction`, `CommRing`, `evalPoly`, `normalForm`, `expand`, `simplify`, `substitute`, `derivative` |
| L24 | `@require` | `target` | `#cpu`, `#contractMismatch` |
| L25 | — | — | `verify`, `explain`, `obligations`, `check` |
| L26 | — | — | `#wasm` |
| L27 | — | `recovery` | `#gpu`, `#cluster`, `nodes:`, `target(…)`, `@require` |
| L31 | — | — | `#mcu` |
| L34 | — | — | `Picture`, `Pointer`, `Keys`, `Midi`, `Camera`, `Audio`, `Sensors`, `#late` |
