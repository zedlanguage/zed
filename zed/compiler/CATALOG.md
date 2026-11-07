# Routines the Rust calls

Plan row PORT-catalog. Every function, method, operator and macro of the Rust standard library or of a dependency that the code of `zedc`, `zed-kernel` and `zed-native` calls, outside unit tests (`#[cfg(test)]`), with what stands for it in Zed. Step S.1 regenerates it over the Rust of its time, and the standard library rows STD-seq, STD-text and STD-num start from it.

The tool `catalog` of `zed-tools` writes the first four columns from a SCIP index that `rust-analyzer scip` makes of this repository, in which every call is resolved to the routine it reaches, operators and trait methods included:

    zrun build/cargo/debug/catalog ../zed zed/compiler/CATALOG.md --write   # regenerate, keeping the Zed column
    zrun build/cargo/debug/catalog ../zed zed/compiler/CATALOG.md           # check

A routine is named `package::module::Type::name`, with an impl's self type and trait written `<T as Trait>`; one Rust routine per row, so `+` on `u32`, on `&u32` and on `BigInt` are three rows. *Uses* counts the call sites, *Files* the files holding them, and *First use* is the first site by path and line.

The Zed column is written by hand and is one of:

- `missing`: nothing in Zed or in the plan provides the routine yet;
- `row ID`: plan rows of `docs/plan_dag.md` that provide it, separated by commas;
- Zed texts in backticks: expressions of the grammar of DESIGN.md whose defined words lie in Zed₀ (layer 24 or below; ZED0.md), with `a`, `b`, `n`, `i`, `x`, `xs`, `ys`, `s`, `t`, `m`, `k`, `f`, `p` and `z` standing for the operands. A text is exact: where Zed and Rust differ, it writes out Rust's result (a truncating `/` on signed integers, a wrapping or saturating operation, a fixed `width:`). `x` alone marks a routine with no work in Zed: a copy, a borrow, a dereference or a shared pointer, which Zed's immutable values make the value itself.

The tool checks every row against the index, so a routine called and not listed, or listed and no longer called, is an error, and checks each Zed column against the grammar, the words table and the plan: each name in a text is an operand, a lambda parameter or a defined word, and each call of a word passes the arguments the word takes (a `width:` where one is required, sort keys or `by:` to `sort`). `missing` entries are allowed until S.1, whose test is that none is left. Plan rows used: STD-seq, STD-text, STD-num and STD-blake3 (the seed library), S.1c (Unicode tables), S.1d (`#bug` for broken invariants), L5.8a (ranges of an ordered family and the priority queue), L6.13 (reuse in place, which replaces capacity and in-place mutation), S.4 (the MLIR text emitter, which replaces Cranelift, `object` and `libc`).

Counts: 1369 routines, 50049 uses.

| Routine | Uses | Files | First use | Zed |
|---|--:|--:|---|---|
| `alloc::borrow::<Cow<'_, B> as Clone>::clone` | 3 | 3 | `crates/zed-kernel/src/bits.rs:248` | `x` |
| `alloc::borrow::<Cow<'_, B> as Deref>::deref` | 30 | 6 | `crates/zed-kernel/src/bits.rs:129` | `x` |
| `alloc::borrow::<Cow<'_, B> as Ord>::cmp` | 2 | 1 | `crates/zed-kernel/src/num.rs:1396` | missing |
| `alloc::borrow::Cow<'_, B>::into_owned` | 12 | 7 | `crates/zed-kernel/src/bits.rs:248` | `x` |
| `alloc::boxed::<Box<T, A> as Clone>::clone` | 4 | 2 | `crates/zedc/src/check/walk.rs:2007` | `x` |
| `alloc::boxed::<Box<T, A> as Deref>::deref` | 75 | 13 | `crates/zed-kernel/src/eval.rs:774` | `x` |
| `alloc::boxed::<Box<T, A> as Ord>::cmp` | 2 | 1 | `crates/zedc/src/store/int.rs:258` | missing |
| `alloc::boxed::<Box<T, A> as PartialEq<Self>>::eq` | 3 | 1 | `crates/zed-kernel/src/num.rs:1452` | `a == b` |
| `alloc::boxed::<Box<[T], A> as Clone>::clone` | 1 | 1 | `crates/zed-kernel/src/num.rs:570` | `x` |
| `alloc::boxed::<Box<[T]> as Default>::default` | 1 | 1 | `crates/zed-kernel/src/num.rs:64` | `[]` |
| `alloc::boxed::Box<T>::new` | 115 | 17 | `crates/zed-kernel/src/deep.rs:172` | `x` |
| `alloc::boxed::Box<T>::pin` | 3 | 2 | `crates/zed-kernel/src/frames.rs:51` | missing |
| `alloc::collections::binary_heap::BinaryHeap<T, A>::clear` | 1 | 1 | `crates/zedc/src/store/negsssp.rs:198` | row L6.13 |
| `alloc::collections::binary_heap::BinaryHeap<T, A>::peek` | 1 | 1 | `crates/zedc/src/store/negsssp.rs:214` | row L5.8a |
| `alloc::collections::binary_heap::BinaryHeap<T, A>::pop` | 7 | 3 | `crates/zedc/src/elab.rs:1238` | row L5.8a |
| `alloc::collections::binary_heap::BinaryHeap<T, A>::push` | 9 | 3 | `crates/zedc/src/elab.rs:1251` | row L6.13 |
| `alloc::collections::binary_heap::BinaryHeap<T>::new` | 1 | 1 | `crates/zedc/src/store/negsssp.rs:190` | row L5.8a |
| `alloc::collections::btree::map::<BTreeMap<K, V, A> as Clone>::clone` | 40 | 12 | `crates/zed-kernel/src/term/walk.rs:53` | `x` |
| `alloc::collections::btree::map::<BTreeMap<K, V, A> as Extend<(K, V)>>::extend` | 5 | 3 | `crates/zed-kernel/src/types/empty.rs:175` | row L6.13 |
| `alloc::collections::btree::map::<BTreeMap<K, V, A> as Index<&Q>>::index` | 124 | 14 | `crates/zed-kernel/src/eval.rs:262` | `xs[i]` |
| `alloc::collections::btree::map::<BTreeMap<K, V, A> as IntoIterator>::into_iter` | 18 | 10 | `crates/zed-kernel/src/eval.rs:1572` | row STD-seq |
| `alloc::collections::btree::map::<BTreeMap<K, V, A> as PartialEq<Self>>::eq` | 15 | 2 | `crates/zedc/src/store/affine.rs:201` | `a == b` |
| `alloc::collections::btree::map::<BTreeMap<K, V> as From<[(K, V); N]>>::from` | 5 | 5 | `crates/zed-kernel/src/provenance.rs:324` | missing |
| `alloc::collections::btree::map::<Iter<'a, K, V> as Iterator>::next` | 7 | 3 | `crates/zedc/src/store/preimage.rs:961` | row STD-seq |
| `alloc::collections::btree::map::<Keys<'a, K, V> as Iterator>::next` | 1 | 1 | `crates/zedc/src/store/hull.rs:276` | row STD-seq |
| `alloc::collections::btree::map::<Range<'a, K, V> as Iterator>::next` | 4 | 2 | `crates/zed-kernel/src/types/bdd.rs:1807` | row L5.8a |
| `alloc::collections::btree::map::<Values<'a, K, V> as Iterator>::next` | 1 | 1 | `crates/zedc/src/store/hull.rs:247` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::clear` | 4 | 2 | `crates/zed-kernel/src/types/empty.rs:155` | row L6.13 |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::contains_key` | 35 | 12 | `crates/zed-kernel/src/eval.rs:888` | `k in m` |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::entry` | 48 | 16 | `crates/zed-kernel/src/eval.rs:1424` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::get` | 125 | 26 | `crates/zed-kernel/src/eval.rs:886` | `xs[i]` |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::get_key_value` | 3 | 2 | `crates/zed-native/src/tables.rs:151` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::get_mut` | 8 | 6 | `crates/zed-kernel/src/eval.rs:1191` | row L6.13 |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::insert` | 101 | 22 | `crates/zed-kernel/src/eval.rs:232` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::into_values` | 6 | 5 | `crates/zed-kernel/src/types/empty.rs:2940` | missing |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::is_empty` | 30 | 10 | `crates/zed-kernel/src/types.rs:174` | `xs.count == 0` |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::iter` | 67 | 15 | `crates/zed-kernel/src/print.rs:307` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::iter_mut` | 1 | 1 | `crates/zedc/src/check/ty.rs:321` | row L6.13 |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::keys` | 54 | 11 | `crates/zed-kernel/src/types.rs:1344` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::len` | 18 | 11 | `crates/zed-kernel/src/types/empty.rs:1943` | `xs.count` |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::pop_last` | 2 | 2 | `crates/zed-kernel/src/provenance.rs:326` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::range` | 6 | 3 | `crates/zed-kernel/src/types/bdd.rs:1803` | row L5.8a |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::remove` | 21 | 11 | `crates/zed-kernel/src/eval.rs:1817` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::retain` | 5 | 3 | `crates/zed-kernel/src/types/empty.rs:1062` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::values` | 36 | 7 | `crates/zed-kernel/src/types.rs:791` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::values_mut` | 2 | 1 | `crates/zedc/src/check/mod.rs:2512` | row L6.13 |
| `alloc::collections::btree::map::BTreeMap<K, V>::new` | 102 | 21 | `crates/zed-kernel/src/eval.rs:1567` | `{}` |
| `alloc::collections::btree::map::entry::Entry<'a, K, V, A>::and_modify` | 1 | 1 | `crates/zedc/src/resolve.rs:230` | row STD-seq |
| `alloc::collections::btree::map::entry::Entry<'a, K, V, A>::or_default` | 23 | 11 | `crates/zed-kernel/src/eval.rs:1424` | row STD-seq |
| `alloc::collections::btree::map::entry::Entry<'a, K, V, A>::or_insert` | 14 | 6 | `crates/zed-kernel/src/family.rs:114` | row STD-seq |
| `alloc::collections::btree::map::entry::Entry<'a, K, V, A>::or_insert_with` | 8 | 5 | `crates/zed-kernel/src/types/empty.rs:1467` | row STD-seq |
| `alloc::collections::btree::map::entry::OccupiedEntry<'a, K, V, A>::get` | 1 | 1 | `crates/zedc/src/zir/lower.rs:396` | row STD-seq |
| `alloc::collections::btree::map::entry::VacantEntry<'a, K, V, A>::insert` | 3 | 2 | `crates/zed-kernel/src/family.rs:144` | row STD-seq |
| `alloc::collections::btree::set::<BTreeSet<T, A> as Clone>::clone` | 8 | 3 | `crates/zedc/src/check/mod.rs:3328` | `x` |
| `alloc::collections::btree::set::<BTreeSet<T, A> as Debug>::fmt` | 1 | 1 | `crates/zedc/src/store/cell.rs:172` | missing |
| `alloc::collections::btree::set::<BTreeSet<T, A> as Extend<T>>::extend` | 32 | 9 | `crates/zed-kernel/src/types/empty.rs:1055` | row L6.13 |
| `alloc::collections::btree::set::<BTreeSet<T, A> as IntoIterator>::into_iter` | 24 | 9 | `crates/zed-kernel/src/eval.rs:1842` | row STD-seq |
| `alloc::collections::btree::set::<BTreeSet<T, A> as PartialEq<Self>>::eq` | 3 | 1 | `crates/zedc/src/store/cell.rs:159` | `a == b` |
| `alloc::collections::btree::set::<BTreeSet<T> as From<[T; N]>>::from` | 5 | 4 | `crates/zed-kernel/src/provenance.rs:308` | missing |
| `alloc::collections::btree::set::<Iter<'a, T> as Iterator>::next` | 3 | 2 | `crates/zedc/src/check/ty.rs:1292` | row STD-seq |
| `alloc::collections::btree::set::<Range<'a, T> as DoubleEndedIterator>::next_back` | 1 | 1 | `crates/zedc/src/store/interval.rs:512` | missing |
| `alloc::collections::btree::set::<Range<'a, T> as Iterator>::next` | 1 | 1 | `crates/zedc/src/store/interval.rs:517` | row L5.8a |
| `alloc::collections::btree::set::BTreeSet<T, A>::clear` | 1 | 1 | `crates/zedc/src/check/ty.rs:3227` | row L6.13 |
| `alloc::collections::btree::set::BTreeSet<T, A>::contains` | 65 | 14 | `crates/zed-kernel/src/eval.rs:1389` | `k in m` |
| `alloc::collections::btree::set::BTreeSet<T, A>::first` | 5 | 2 | `crates/zedc/src/check/ty.rs:503` | `xs.first` |
| `alloc::collections::btree::set::BTreeSet<T, A>::get` | 1 | 1 | `crates/zed-kernel/src/provenance.rs:508` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::insert` | 78 | 15 | `crates/zed-kernel/src/eval.rs:1759` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::intersection` | 3 | 2 | `crates/zedc/src/store/affine.rs:502` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::is_disjoint` | 1 | 1 | `crates/zedc/src/store/product.rs:2136` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::is_empty` | 38 | 8 | `crates/zed-kernel/src/types/empty.rs:1046` | `xs.count == 0` |
| `alloc::collections::btree::set::BTreeSet<T, A>::iter` | 82 | 13 | `crates/zed-kernel/src/types/empty.rs:1051` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::len` | 7 | 3 | `crates/zed-kernel/src/types/empty.rs:589` | `xs.count` |
| `alloc::collections::btree::set::BTreeSet<T, A>::pop_last` | 2 | 1 | `crates/zedc/src/stage.rs:1843` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::range` | 6 | 3 | `crates/zedc/src/store/affine.rs:436` | row L5.8a |
| `alloc::collections::btree::set::BTreeSet<T, A>::remove` | 17 | 6 | `crates/zed-kernel/src/eval.rs:1753` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::retain` | 2 | 2 | `crates/zed-kernel/src/types/empty.rs:2888` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::union` | 1 | 1 | `crates/zedc/src/store/lattice.rs:327` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T>::new` | 72 | 15 | `crates/zed-kernel/src/provenance.rs:304` | `{}` |
| `alloc::collections::vec_deque::VecDeque<T, A>::back` | 1 | 1 | `crates/zedc/src/ast/mod.rs:565` | `xs.last` |
| `alloc::collections::vec_deque::VecDeque<T, A>::get_mut` | 1 | 1 | `crates/zedc/src/ast/mod.rs:649` | row L6.13 |
| `alloc::collections::vec_deque::VecDeque<T, A>::is_empty` | 1 | 1 | `crates/zedc/src/store/product.rs:1826` | `xs.count == 0` |
| `alloc::collections::vec_deque::VecDeque<T, A>::iter` | 1 | 1 | `crates/zedc/src/store/product.rs:1756` | row STD-seq |
| `alloc::collections::vec_deque::VecDeque<T, A>::pop_back` | 1 | 1 | `crates/zedc/src/ast/mod.rs:566` | row STD-seq |
| `alloc::collections::vec_deque::VecDeque<T, A>::pop_front` | 2 | 1 | `crates/zedc/src/store/product.rs:1761` | row STD-seq |
| `alloc::collections::vec_deque::VecDeque<T, A>::push_back` | 2 | 1 | `crates/zedc/src/store/product.rs:1787` | row L6.13 |
| `alloc::collections::vec_deque::VecDeque<T, A>::push_front` | 1 | 1 | `crates/zedc/src/ast/mod.rs:563` | missing |
| `alloc::collections::vec_deque::VecDeque<T>::new` | 1 | 1 | `crates/zedc/src/ast/mod.rs:536` | `[]` |
| `alloc::io::read::Read::read_to_end` | 1 | 1 | `crates/zedc/src/run.rs:1040` | missing |
| `alloc::macros::format!` | 841 | 57 | `crates/zed-kernel/src/bits.rs:51` | `"${x}"` |
| `alloc::macros::vec!` | 988 | 82 | `crates/zed-kernel/src/deep.rs:613` | missing |
| `alloc::rc::<Rc<T, A> as AsRef<T>>::as_ref` | 1 | 1 | `crates/zedc/src/check/walk.rs:2042` | `x` |
| `alloc::rc::<Rc<T, A> as Clone>::clone` | 42 | 8 | `crates/zed-kernel/src/eval.rs:834` | `x` |
| `alloc::rc::<Rc<T, A> as Deref>::deref` | 30 | 4 | `crates/zedc/src/check/mod.rs:955` | `x` |
| `alloc::rc::<Rc<T, A> as PartialOrd<Self>>::lt` | 6 | 1 | `crates/zedc/src/store/presburger.rs:4188` | `a < b` |
| `alloc::rc::<Rc<T> as Default>::default` | 1 | 1 | `crates/zed-kernel/src/eval.rs:379` | missing |
| `alloc::rc::Rc<T, A>::as_ptr` | 1 | 1 | `crates/zedc/src/store/presburger.rs:5926` | missing |
| `alloc::rc::Rc<T, A>::ptr_eq` | 2 | 1 | `crates/zedc/src/store/preimage.rs:3804` | row L6.13 |
| `alloc::rc::Rc<T, A>::try_unwrap` | 3 | 3 | `crates/zedc/src/check/mod.rs:473` | row L6.13 |
| `alloc::rc::Rc<T>::new` | 35 | 8 | `crates/zed-kernel/src/eval.rs:829` | `x` |
| `alloc::slice::[T]::concat` | 13 | 7 | `crates/zed-kernel/src/num.rs:138` | row STD-seq |
| `alloc::slice::[T]::join` | 74 | 32 | `crates/zed-kernel/src/bits.rs:82` | row STD-text |
| `alloc::slice::[T]::sort` | 18 | 12 | `crates/zed-kernel/src/eval.rs:1821` | `xs.sort(asc x -> x)` |
| `alloc::slice::[T]::sort_by` | 16 | 12 | `crates/zed-kernel/src/value.rs:365` | `xs.sort(by: f)` |
| `alloc::slice::[T]::sort_by_cached_key` | 1 | 1 | `crates/zedc/src/zir/text.rs:382` | `xs.sort(asc f)` |
| `alloc::slice::[T]::sort_by_key` | 21 | 12 | `crates/zedc/src/ast/mod.rs:386` | `xs.sort(asc f)` |
| `alloc::slice::[T]::to_vec` | 47 | 25 | `crates/zed-kernel/src/eval.rs:937` | `x` |
| `alloc::str::<str as ToOwned>::to_owned` | 1 | 1 | `crates/zedc/src/store/presburger.rs:1211` | `x` |
| `alloc::str::str::repeat` | 9 | 4 | `crates/zed-kernel/src/num.rs:1304` | row STD-text |
| `alloc::str::str::replace` | 5 | 3 | `crates/zedc/src/lex/number.rs:60` | row L6.13 |
| `alloc::str::str::to_lowercase` | 1 | 1 | `crates/zed-kernel/src/words.rs:121` | `lower(s)` |
| `alloc::str::str::to_uppercase` | 1 | 1 | `crates/zed-kernel/src/words.rs:122` | `upper(s)` |
| `alloc::string::<&str as PartialEq<String>>::ne` | 3 | 1 | `crates/zedc/src/zir/text.rs:367` | `a != b` |
| `alloc::string::<String as AddAssign<&str>>::add_assign` | 15 | 1 | `crates/zed-kernel/src/print.rs:787` | `s ++ t` |
| `alloc::string::<String as Clone>::clone` | 54 | 16 | `crates/zed-kernel/src/types/print.rs:1023` | `x` |
| `alloc::string::<String as Deref>::deref` | 5 | 2 | `crates/zedc/src/check/walk.rs:1904` | `x` |
| `alloc::string::<String as From<&str>>::from` | 4 | 3 | `crates/zed-native/src/tables.rs:311` | `x` |
| `alloc::string::<String as Index<I>>::index` | 6 | 3 | `crates/zedc/src/check/read.rs:61` | `fromUtf8(utf8(s).drop(a).take(b - a))` |
| `alloc::string::<String as Ord>::cmp` | 4 | 4 | `crates/zed-kernel/src/types/rec.rs:908` | missing |
| `alloc::string::<String as PartialEq<&str>>::eq` | 27 | 7 | `crates/zed-kernel/src/num.rs:1488` | `a == b` |
| `alloc::string::<T as ToString>::to_string` | 161 | 47 | `crates/zed-kernel/src/eval.rs:891` | `"${x}"` |
| `alloc::string::String::as_bytes` | 13 | 8 | `crates/zed-kernel/src/types.rs:148` | `utf8(s)` |
| `alloc::string::String::as_str` | 79 | 22 | `crates/zed-kernel/src/text.rs:311` | `x` |
| `alloc::string::String::clear` | 1 | 1 | `crates/zed-native/src/tables.rs:215` | row L6.13 |
| `alloc::string::String::from_utf8` | 3 | 2 | `crates/zed-kernel/src/words.rs:182` | `fromUtf8(b)` |
| `alloc::string::String::from_utf8_lossy` | 2 | 2 | `crates/zed-native/src/link.rs:151` | missing |
| `alloc::string::String::into_bytes` | 1 | 1 | `crates/zedc/src/testing.rs:264` | `utf8(s)` |
| `alloc::string::String::is_empty` | 6 | 5 | `crates/zedc/src/elab/walk.rs:1853` | `len(s) == 0` |
| `alloc::string::String::len` | 18 | 11 | `crates/zed-kernel/src/num.rs:1561` | `utf8(s).count` |
| `alloc::string::String::new` | 34 | 24 | `crates/zed-kernel/src/print.rs:25` | `""` |
| `alloc::string::String::push` | 13 | 6 | `crates/zed-kernel/src/types/print.rs:1045` | row L6.13 |
| `alloc::string::String::push_str` | 44 | 13 | `crates/zed-kernel/src/num.rs:1304` | `s ++ t` |
| `alloc::string::String::truncate` | 7 | 3 | `crates/zedc/src/zir/lower.rs:1683` | row L6.13 |
| `alloc::string::String::try_reserve_exact` | 2 | 2 | `crates/zed-kernel/src/words.rs:251` | row L6.13 |
| `alloc::string::String::with_capacity` | 3 | 3 | `crates/zed-kernel/src/text.rs:140` | row L6.13 |
| `alloc::sync::<Arc<T, A> as AsRef<T>>::as_ref` | 4 | 2 | `crates/zedc/src/check/mod.rs:2726` | `x` |
| `alloc::sync::<Arc<T, A> as Clone>::clone` | 483 | 38 | `crates/zed-kernel/src/deep.rs:351` | `x` |
| `alloc::sync::<Arc<T, A> as Deref>::deref` | 128 | 37 | `crates/zed-kernel/src/eval.rs:886` | `x` |
| `alloc::sync::<Arc<T, A> as Ord>::cmp` | 9 | 5 | `crates/zed-kernel/src/deep.rs:155` | missing |
| `alloc::sync::<Arc<T, A> as PartialEq<Self>>::eq` | 36 | 8 | `crates/zed-kernel/src/eval.rs:2011` | `a == b` |
| `alloc::sync::<Arc<T, A> as PartialEq<Self>>::ne` | 6 | 2 | `crates/zed-kernel/src/types/empty.rs:1180` | `a != b` |
| `alloc::sync::<Arc<[T], A> as From<Vec<T, A>>>::from` | 2 | 1 | `crates/zed-kernel/src/types.rs:1508` | `x` |
| `alloc::sync::<Arc<[T]> as From<[T; N]>>::from` | 1 | 1 | `crates/zedc/src/run.rs:481` | `x` |
| `alloc::sync::<Arc<str> as From<&str>>::from` | 9 | 7 | `crates/zed-kernel/src/term.rs:531` | `x` |
| `alloc::sync::<Arc<str> as From<String>>::from` | 4 | 4 | `crates/zed-kernel/src/text.rs:305` | `x` |
| `alloc::sync::Arc<T, A>::as_ptr` | 13 | 5 | `crates/zed-kernel/src/types.rs:469` | missing |
| `alloc::sync::Arc<T, A>::get_mut` | 9 | 6 | `crates/zed-kernel/src/term.rs:371` | row L6.13 |
| `alloc::sync::Arc<T, A>::into_inner` | 4 | 3 | `crates/zed-kernel/src/provenance.rs:92` | `x` |
| `alloc::sync::Arc<T, A>::make_mut` | 5 | 2 | `crates/zed-kernel/src/term.rs:354` | row L6.13 |
| `alloc::sync::Arc<T, A>::ptr_eq` | 17 | 9 | `crates/zed-kernel/src/provenance.rs:105` | row L6.13 |
| `alloc::sync::Arc<T, A>::strong_count` | 5 | 4 | `crates/zed-kernel/src/term.rs:366` | row L6.13 |
| `alloc::sync::Arc<T, A>::try_unwrap` | 1 | 1 | `crates/zedc/src/store/cell.rs:144` | row L6.13 |
| `alloc::sync::Arc<T, A>::unwrap_or_clone` | 3 | 3 | `crates/zed-kernel/src/term.rs:361` | `x` |
| `alloc::sync::Arc<T>::new` | 75 | 23 | `crates/zed-kernel/src/provenance.rs:53` | `x` |
| `alloc::vec::<Vec<T, A> as Clone>::clone` | 72 | 25 | `crates/zed-kernel/src/eval.rs:1486` | `x` |
| `alloc::vec::<Vec<T, A> as Clone>::clone_from` | 2 | 1 | `crates/zed-kernel/src/types/bes.rs:792` | `x` |
| `alloc::vec::<Vec<T, A> as Deref>::deref` | 2 | 2 | `crates/zedc/src/store/presburger.rs:4630` | `x` |
| `alloc::vec::<Vec<T, A> as Extend<&'a T>>::extend` | 2 | 2 | `crates/zedc/src/elab.rs:147` | row L6.13 |
| `alloc::vec::<Vec<T, A> as Extend<T>>::extend` | 576 | 60 | `crates/zed-kernel/src/deep.rs:70` | row L6.13 |
| `alloc::vec::<Vec<T, A> as Index<I>>::index` | 3090 | 60 | `crates/zed-kernel/src/eval.rs:424` | `xs[i]` |
| `alloc::vec::<Vec<T, A> as IndexMut<I>>::index_mut` | 1136 | 46 | `crates/zed-kernel/src/family.rs:114` | row L6.13 |
| `alloc::vec::<Vec<T, A> as IntoIterator>::into_iter` | 282 | 53 | `crates/zed-kernel/src/eval.rs:815` | row STD-seq |
| `alloc::vec::<Vec<T, A> as Ord>::cmp` | 6 | 4 | `crates/zed-kernel/src/types/rec.rs:908` | missing |
| `alloc::vec::<Vec<T> as FromIterator<T>>::from_iter` | 1 | 1 | `crates/zedc/src/store/presburger.rs:5225` | `x` |
| `alloc::vec::<[T; N] as TryFrom<Vec<T, A>>>::try_from` | 7 | 5 | `crates/zed-kernel/src/eval.rs:1370` | missing |
| `alloc::vec::Vec<T, A>::append` | 15 | 10 | `crates/zed-kernel/src/family.rs:258` | row L6.13 |
| `alloc::vec::Vec<T, A>::as_slice` | 30 | 14 | `crates/zed-kernel/src/eval.rs:2181` | `x` |
| `alloc::vec::Vec<T, A>::clear` | 38 | 16 | `crates/zed-kernel/src/eval.rs:370` | row L6.13 |
| `alloc::vec::Vec<T, A>::dedup` | 25 | 13 | `crates/zed-kernel/src/types/bdd.rs:396` | row STD-seq |
| `alloc::vec::Vec<T, A>::dedup_by` | 3 | 3 | `crates/zedc/src/elab.rs:317` | row STD-seq |
| `alloc::vec::Vec<T, A>::drain` | 17 | 12 | `crates/zed-kernel/src/print.rs:678` | missing |
| `alloc::vec::Vec<T, A>::extend_from_slice` | 31 | 11 | `crates/zed-native/src/codegen.rs:367` | row L6.13 |
| `alloc::vec::Vec<T, A>::insert` | 4 | 3 | `crates/zed-kernel/src/types/bdd.rs:1653` | row STD-seq |
| `alloc::vec::Vec<T, A>::into_boxed_slice` | 3 | 2 | `crates/zed-kernel/src/num.rs:104` | row L6.13 |
| `alloc::vec::Vec<T, A>::is_empty` | 265 | 50 | `crates/zed-kernel/src/eval.rs:1796` | `xs.count == 0` |
| `alloc::vec::Vec<T, A>::len` | 880 | 69 | `crates/zed-kernel/src/eval.rs:422` | `xs.count` |
| `alloc::vec::Vec<T, A>::pop` | 405 | 68 | `crates/zed-kernel/src/deep.rs:81` | row STD-seq |
| `alloc::vec::Vec<T, A>::pop_if` | 1 | 1 | `crates/zedc/src/store/preimage.rs:1895` | missing |
| `alloc::vec::Vec<T, A>::push` | 1866 | 87 | `crates/zed-kernel/src/deep.rs:168` | row L6.13 |
| `alloc::vec::Vec<T, A>::remove` | 10 | 8 | `crates/zed-kernel/src/eval.rs:935` | row STD-seq |
| `alloc::vec::Vec<T, A>::resize` | 7 | 6 | `crates/zedc/src/ast/mod.rs:555` | missing |
| `alloc::vec::Vec<T, A>::resize_with` | 5 | 4 | `crates/zed-kernel/src/family.rs:172` | missing |
| `alloc::vec::Vec<T, A>::retain` | 10 | 6 | `crates/zedc/src/check/ty.rs:1742` | row STD-seq |
| `alloc::vec::Vec<T, A>::splice` | 3 | 2 | `crates/zed-kernel/src/types/bdd.rs:1714` | missing |
| `alloc::vec::Vec<T, A>::split_off` | 15 | 10 | `crates/zed-kernel/src/term/walk.rs:106` | missing |
| `alloc::vec::Vec<T, A>::swap_remove` | 8 | 7 | `crates/zed-kernel/src/family.rs:181` | missing |
| `alloc::vec::Vec<T, A>::truncate` | 35 | 12 | `crates/zed-kernel/src/eval.rs:1732` | row L6.13 |
| `alloc::vec::Vec<T, A>::try_reserve_exact` | 1 | 1 | `crates/zed-kernel/src/num.rs:1280` | row L6.13 |
| `alloc::vec::Vec<T>::new` | 789 | 80 | `crates/zed-kernel/src/deep.rs:38` | `[]` |
| `alloc::vec::Vec<T>::with_capacity` | 94 | 35 | `crates/zed-kernel/src/deep.rs:372` | row L6.13 |
| `alloc::vec::drain::<Drain<'_, T, A> as Iterator>::next` | 2 | 1 | `crates/zedc/src/canon/binders.rs:668` | row STD-seq |
| `alloc::vec::into_iter::<IntoIter<T, A> as Iterator>::fold` | 6 | 3 | `crates/zed-kernel/src/provenance.rs:240` | `xs.foldl(z, f)` |
| `alloc::vec::into_iter::<IntoIter<T, A> as Iterator>::next` | 38 | 16 | `crates/zed-kernel/src/eval.rs:1029` | row STD-seq |
| `alloc::vec::partial_eq::<Vec<T, A1> as PartialEq<Vec<U, A2>>>::eq` | 33 | 7 | `crates/zed-kernel/src/types/rec.rs:364` | `a == b` |
| `alloc::vec::partial_eq::<Vec<T, A1> as PartialEq<Vec<U, A2>>>::ne` | 18 | 3 | `crates/zedc/src/ast/types.rs:163` | `a != b` |
| `alloc::vec::partial_eq::<Vec<T, A> as PartialEq<&[U]>>::eq` | 6 | 1 | `crates/zedc/src/zir/text.rs:598` | `a == b` |
| `blake3::Hash::as_bytes` | 1 | 1 | `crates/zedc/src/address.rs:35` | row STD-blake3 |
| `blake3::Hasher::finalize` | 1 | 1 | `crates/zedc/src/address.rs:35` | row STD-blake3 |
| `blake3::Hasher::new` | 5 | 2 | `crates/zedc/src/canon/mod.rs:198` | row STD-blake3 |
| `blake3::Hasher::update` | 22 | 2 | `crates/zedc/src/canon/mod.rs:199` | row STD-blake3 |
| `core::any::TypeId::of` | 1 | 1 | `crates/zed-native/src/link.rs:211` | missing |
| `core::array::<[T; N] as Clone>::clone` | 8 | 1 | `crates/zedc/src/store/live3.rs:318` | `x` |
| `core::array::<[T; N] as Index<I>>::index` | 248 | 18 | `crates/zed-kernel/src/bits.rs:175` | `xs[i]` |
| `core::array::<[T; N] as IndexMut<I>>::index_mut` | 68 | 10 | `crates/zed-kernel/src/exact.rs:37` | row L6.13 |
| `core::array::<[T; N] as PartialOrd<Self>>::lt` | 12 | 1 | `crates/zedc/src/store/live3.rs:412` | `a < b` |
| `core::array::<[T; _] as Default>::default` | 1 | 1 | `crates/zedc/src/store/revision.rs:331` | missing |
| `core::array::[T; N]::as_slice` | 1 | 1 | `crates/zedc/src/store/presburger.rs:4337` | `x` |
| `core::array::[T; N]::each_ref` | 1 | 1 | `crates/zedc/src/store/live3.rs:879` | missing |
| `core::array::[T; N]::map` | 60 | 14 | `crates/zed-kernel/src/eval.rs:970` | missing |
| `core::array::iter::<[T; N] as IntoIterator>::into_iter` | 55 | 26 | `crates/zed-kernel/src/exact.rs:16` | row STD-seq |
| `core::bool::bool::then` | 55 | 20 | `crates/zed-kernel/src/deep.rs:408` | missing |
| `core::bool::bool::then_some` | 50 | 21 | `crates/zed-kernel/src/num.rs:1633` | missing |
| `core::borrow::Borrow::borrow` | 5 | 2 | `crates/zedc/src/store/live3.rs:255` | `x` |
| `core::cell::<RefCell<T> as Default>::default` | 3 | 1 | `crates/zed-kernel/src/eval.rs:1672` | missing |
| `core::cell::<RefMut<'_, T> as DerefMut>::deref_mut` | 3 | 2 | `crates/zed-kernel/src/types/empty.rs:1341` | `x` |
| `core::cell::Cell<T>::get` | 4 | 4 | `crates/zed-kernel/src/family.rs:48` | missing |
| `core::cell::Cell<T>::new` | 15 | 8 | `crates/zed-kernel/src/deep.rs:36` | missing |
| `core::cell::Cell<T>::replace` | 2 | 2 | `crates/zed-kernel/src/deep.rs:69` | row L6.13 |
| `core::cell::Cell<T>::set` | 9 | 7 | `crates/zed-kernel/src/deep.rs:84` | missing |
| `core::cell::Cell<T>::take` | 3 | 1 | `crates/zed-kernel/src/frames.rs:85` | row L6.13 |
| `core::cell::RefCell<T>::borrow` | 9 | 2 | `crates/zed-kernel/src/eval.rs:1381` | `x` |
| `core::cell::RefCell<T>::borrow_mut` | 28 | 7 | `crates/zed-kernel/src/deep.rs:70` | `x` |
| `core::cell::RefCell<T>::into_inner` | 2 | 2 | `crates/zed-kernel/src/types.rs:936` | `x` |
| `core::cell::RefCell<T>::new` | 15 | 7 | `crates/zed-kernel/src/deep.rs:38` | missing |
| `core::cell::RefCell<T>::take` | 2 | 1 | `crates/zed-kernel/src/eval.rs:1842` | row L6.13 |
| `core::cell::once::OnceCell<T>::get` | 4 | 1 | `crates/zedc/src/store/presburger.rs:2703` | missing |
| `core::cell::once::OnceCell<T>::get_or_init` | 5 | 3 | `crates/zedc/src/ast/body.rs:207` | missing |
| `core::cell::once::OnceCell<T>::new` | 8 | 3 | `crates/zedc/src/ast/mod.rs:426` | missing |
| `core::cell::once::OnceCell<T>::set` | 1 | 1 | `crates/zedc/src/store/presburger.rs:2727` | missing |
| `core::char::convert::<u32 as From<char>>::from` | 2 | 2 | `crates/zed-kernel/src/words.rs:126` | `int(x)` |
| `core::char::methods::char::encode_utf8` | 1 | 1 | `crates/zed-kernel/src/words.rs:130` | missing |
| `core::char::methods::char::from_u32` | 4 | 3 | `crates/zed-kernel/src/words.rs:129` | missing |
| `core::char::methods::char::is_alphabetic` | 1 | 1 | `crates/zedc/src/docs.rs:82` | missing |
| `core::char::methods::char::is_alphanumeric` | 3 | 3 | `crates/zedc/src/ast/neglit.rs:147` | missing |
| `core::char::methods::char::is_ascii_alphabetic` | 1 | 1 | `crates/zedc/src/parse/grammar.rs:397` | missing |
| `core::char::methods::char::is_ascii_alphanumeric` | 2 | 1 | `crates/zedc/src/parse/grammar.rs:135` | missing |
| `core::char::methods::char::is_ascii_digit` | 10 | 6 | `crates/zedc/src/ast/neglit.rs:157` | missing |
| `core::char::methods::char::is_digit` | 2 | 2 | `crates/zed-kernel/src/value.rs:441` | missing |
| `core::char::methods::char::is_whitespace` | 2 | 2 | `crates/zedc/src/ast/neglit.rs:165` | missing |
| `core::char::methods::char::len_utf8` | 7 | 3 | `crates/zedc/src/lex/comment.rs:34` | `utf8(s).count` |
| `core::clone::Clone::clone` | 46 | 11 | `crates/zed-kernel/src/types/bdd.rs:183` | `x` |
| `core::clone::impls::<usize as Clone>::clone` | 1 | 1 | `crates/zedc/src/canon/binders.rs:331` | `x` |
| `core::cmp::<Ordering as PartialEq<Self>>::eq` | 81 | 11 | `crates/zed-kernel/src/num.rs:675` | `a == b` |
| `core::cmp::Ord::clamp` | 1 | 1 | `crates/zed-kernel/src/num/bound.rs:353` | `min(max(x, a), b)` |
| `core::cmp::Ord::cmp` | 3 | 2 | `crates/zed-kernel/src/types/bdd.rs:281` | missing |
| `core::cmp::Ord::max` | 82 | 28 | `crates/zed-kernel/src/eval.rs:2246` | `max(a, b)` |
| `core::cmp::Ord::min` | 78 | 31 | `crates/zed-kernel/src/bits.rs:210` | `min(a, b)` |
| `core::cmp::Ordering::is_eq` | 3 | 3 | `crates/zed-kernel/src/types.rs:1539` | missing |
| `core::cmp::Ordering::is_gt` | 3 | 1 | `crates/zedc/src/store/live3.rs:383` | missing |
| `core::cmp::Ordering::is_le` | 1 | 1 | `crates/zed-kernel/src/types/bdd.rs:673` | missing |
| `core::cmp::Ordering::is_ne` | 9 | 3 | `crates/zed-kernel/src/types/rec.rs:876` | missing |
| `core::cmp::Ordering::reverse` | 8 | 3 | `crates/zed-kernel/src/num.rs:1382` | missing |
| `core::cmp::Ordering::then` | 10 | 6 | `crates/zed-kernel/src/provenance.rs:142` | missing |
| `core::cmp::Ordering::then_with` | 21 | 9 | `crates/zed-kernel/src/deep.rs:155` | missing |
| `core::cmp::PartialEq::eq` | 18 | 5 | `crates/zedc/src/canon/mod.rs:113` | `a == b` |
| `core::cmp::PartialEq::ne` | 420 | 35 | `crates/zed-kernel/src/num.rs:1377` | `a != b` |
| `core::cmp::PartialOrd::ge` | 60 | 11 | `crates/zed-kernel/src/bits.rs:129` | `a >= b` |
| `core::cmp::PartialOrd::gt` | 84 | 15 | `crates/zed-kernel/src/num.rs:57` | `a > b` |
| `core::cmp::PartialOrd::le` | 90 | 13 | `crates/zed-kernel/src/num.rs:240` | `a <= b` |
| `core::cmp::PartialOrd::lt` | 123 | 13 | `crates/zed-kernel/src/bits.rs:154` | `a < b` |
| `core::cmp::impls::<&A as PartialEq<&B>>::eq` | 552 | 51 | `crates/zed-kernel/src/deep.rs:487` | `a == b` |
| `core::cmp::impls::<&A as PartialEq<&B>>::ne` | 120 | 22 | `crates/zed-kernel/src/types/empty.rs:318` | `a != b` |
| `core::cmp::impls::<&A as PartialOrd<&B>>::ge` | 18 | 4 | `crates/zedc/src/store/int.rs:393` | `a >= b` |
| `core::cmp::impls::<&A as PartialOrd<&B>>::gt` | 23 | 5 | `crates/zedc/src/store/preimage.rs:696` | `a > b` |
| `core::cmp::impls::<&A as PartialOrd<&B>>::le` | 33 | 6 | `crates/zedc/src/cost.rs:184` | `a <= b` |
| `core::cmp::impls::<&A as PartialOrd<&B>>::lt` | 25 | 5 | `crates/zedc/src/store/interval.rs:534` | `a < b` |
| `core::cmp::impls::<&mut A as PartialEq<&B>>::eq` | 3 | 1 | `crates/zed-kernel/src/types/empty.rs:1964` | `a == b` |
| `core::cmp::impls::<bool as Ord>::cmp` | 14 | 4 | `crates/zed-kernel/src/num.rs:1391` | missing |
| `core::cmp::impls::<bool as PartialEq<Self>>::eq` | 147 | 12 | `crates/zed-kernel/src/eval.rs:2130` | `a == b` |
| `core::cmp::impls::<bool as PartialEq<Self>>::ne` | 60 | 11 | `crates/zed-kernel/src/types.rs:1127` | `a != b` |
| `core::cmp::impls::<char as PartialEq<Self>>::eq` | 78 | 9 | `crates/zedc/src/ast/neglit.rs:147` | `a == b` |
| `core::cmp::impls::<char as PartialEq<Self>>::ne` | 12 | 3 | `crates/zed-kernel/src/num.rs:1560` | `a != b` |
| `core::cmp::impls::<char as PartialOrd<Self>>::le` | 6 | 1 | `crates/zedc/src/parse/engine.rs:640` | `a <= b` |
| `core::cmp::impls::<f64 as PartialEq<Self>>::eq` | 21 | 6 | `crates/zed-kernel/src/deep.rs:184` | `a == b` |
| `core::cmp::impls::<f64 as PartialOrd<Self>>::ge` | 3 | 1 | `crates/zed-kernel/src/eval.rs:2225` | `a >= b` |
| `core::cmp::impls::<f64 as PartialOrd<Self>>::gt` | 15 | 4 | `crates/zed-kernel/src/eval.rs:2224` | `a > b` |
| `core::cmp::impls::<f64 as PartialOrd<Self>>::le` | 3 | 1 | `crates/zed-kernel/src/eval.rs:2223` | `a <= b` |
| `core::cmp::impls::<f64 as PartialOrd<Self>>::lt` | 9 | 2 | `crates/zed-kernel/src/eval.rs:2132` | `a < b` |
| `core::cmp::impls::<f64 as PartialOrd<Self>>::partial_cmp` | 1 | 1 | `crates/zed-kernel/src/deep.rs:189` | missing |
| `core::cmp::impls::<i128 as Ord>::clamp` | 1 | 1 | `crates/zedc/src/store/preimage.rs:1774` | `min(max(x, a), b)` |
| `core::cmp::impls::<i128 as Ord>::cmp` | 1 | 1 | `crates/zedc/src/store/int.rs:257` | missing |
| `core::cmp::impls::<i128 as PartialEq<Self>>::eq` | 27 | 4 | `crates/zedc/src/check/widen.rs:724` | `a == b` |
| `core::cmp::impls::<i128 as PartialEq<Self>>::ne` | 12 | 2 | `crates/zed-kernel/src/types/empty.rs:772` | `a != b` |
| `core::cmp::impls::<i128 as PartialOrd<Self>>::ge` | 3 | 1 | `crates/zedc/src/store/preimage.rs:4870` | `a >= b` |
| `core::cmp::impls::<i128 as PartialOrd<Self>>::gt` | 24 | 2 | `crates/zedc/src/store/int.rs:126` | `a > b` |
| `core::cmp::impls::<i128 as PartialOrd<Self>>::le` | 21 | 1 | `crates/zedc/src/store/preimage.rs:745` | `a <= b` |
| `core::cmp::impls::<i128 as PartialOrd<Self>>::lt` | 21 | 3 | `crates/zedc/src/check/widen.rs:792` | `a < b` |
| `core::cmp::impls::<i32 as PartialEq<Self>>::eq` | 21 | 5 | `crates/zed-kernel/src/types/bdd.rs:1185` | `a == b` |
| `core::cmp::impls::<i32 as PartialOrd<Self>>::ge` | 3 | 1 | `crates/zedc/src/store/float.rs:58` | `a >= b` |
| `core::cmp::impls::<i32 as PartialOrd<Self>>::gt` | 9 | 3 | `crates/zedc/src/check/mod.rs:4539` | `a > b` |
| `core::cmp::impls::<i32 as PartialOrd<Self>>::le` | 3 | 1 | `crates/zed-kernel/src/num.rs:1565` | `a <= b` |
| `core::cmp::impls::<i32 as PartialOrd<Self>>::lt` | 6 | 2 | `crates/zed-kernel/src/num.rs:1563` | `a < b` |
| `core::cmp::impls::<i64 as Ord>::cmp` | 2 | 2 | `crates/zed-kernel/src/value.rs:600` | missing |
| `core::cmp::impls::<i64 as PartialEq<Self>>::eq` | 84 | 9 | `crates/zed-kernel/src/bits.rs:199` | `a == b` |
| `core::cmp::impls::<i64 as PartialEq<Self>>::ne` | 15 | 4 | `crates/zed-kernel/src/eval.rs:2068` | `a != b` |
| `core::cmp::impls::<i64 as PartialOrd<Self>>::ge` | 21 | 5 | `crates/zed-kernel/src/num.rs:1533` | `a >= b` |
| `core::cmp::impls::<i64 as PartialOrd<Self>>::gt` | 27 | 4 | `crates/zed-kernel/src/bits.rs:183` | `a > b` |
| `core::cmp::impls::<i64 as PartialOrd<Self>>::le` | 33 | 2 | `crates/zed-kernel/src/bits.rs:202` | `a <= b` |
| `core::cmp::impls::<i64 as PartialOrd<Self>>::lt` | 21 | 3 | `crates/zed-kernel/src/bits.rs:175` | `a < b` |
| `core::cmp::impls::<i8 as Ord>::cmp` | 3 | 2 | `crates/zedc/src/store/int.rs:2409` | missing |
| `core::cmp::impls::<i8 as PartialEq<Self>>::eq` | 12 | 2 | `crates/zedc/src/store/int.rs:2169` | `a == b` |
| `core::cmp::impls::<i8 as PartialEq<Self>>::ne` | 6 | 1 | `crates/zedc/src/store/revision.rs:211` | `a != b` |
| `core::cmp::impls::<i8 as PartialOrd<Self>>::ge` | 21 | 2 | `crates/zedc/src/check/mod.rs:5660` | `a >= b` |
| `core::cmp::impls::<i8 as PartialOrd<Self>>::gt` | 15 | 2 | `crates/zedc/src/store/interval.rs:645` | `a > b` |
| `core::cmp::impls::<i8 as PartialOrd<Self>>::le` | 3 | 1 | `crates/zedc/src/store/preimage.rs:5823` | `a <= b` |
| `core::cmp::impls::<i8 as PartialOrd<Self>>::lt` | 36 | 4 | `crates/zedc/src/store/affine.rs:99` | `a < b` |
| `core::cmp::impls::<isize as PartialOrd<Self>>::gt` | 3 | 1 | `crates/zedc/src/store/presburger.rs:5000` | `a > b` |
| `core::cmp::impls::<isize as PartialOrd<Self>>::le` | 9 | 1 | `crates/zedc/src/store/presburger.rs:4372` | `a <= b` |
| `core::cmp::impls::<u128 as PartialEq<Self>>::eq` | 3 | 1 | `crates/zed-kernel/src/num.rs:1192` | `a == b` |
| `core::cmp::impls::<u128 as PartialEq<Self>>::ne` | 3 | 1 | `crates/zed-kernel/src/exact.rs:22` | `a != b` |
| `core::cmp::impls::<u128 as PartialOrd<Self>>::ge` | 3 | 1 | `crates/zed-kernel/src/num.rs:923` | `a >= b` |
| `core::cmp::impls::<u128 as PartialOrd<Self>>::le` | 9 | 2 | `crates/zedc/src/store/negsssp.rs:353` | `a <= b` |
| `core::cmp::impls::<u32 as Ord>::cmp` | 2 | 1 | `crates/zed-kernel/src/provenance.rs:138` | missing |
| `core::cmp::impls::<u32 as PartialEq<Self>>::eq` | 258 | 16 | `crates/zed-kernel/src/bits.rs:218` | `a == b` |
| `core::cmp::impls::<u32 as PartialEq<Self>>::ne` | 78 | 10 | `crates/zed-kernel/src/provenance.rs:100` | `a != b` |
| `core::cmp::impls::<u32 as PartialOrd<Self>>::ge` | 6 | 2 | `crates/zed-kernel/src/exact.rs:84` | `a >= b` |
| `core::cmp::impls::<u32 as PartialOrd<Self>>::gt` | 46 | 8 | `crates/zed-kernel/src/provenance.rs:125` | `a > b` |
| `core::cmp::impls::<u32 as PartialOrd<Self>>::le` | 9 | 2 | `crates/zedc/src/check/widen.rs:552` | `a <= b` |
| `core::cmp::impls::<u32 as PartialOrd<Self>>::lt` | 9 | 3 | `crates/zed-kernel/src/exact.rs:62` | `a < b` |
| `core::cmp::impls::<u64 as Ord>::cmp` | 16 | 4 | `crates/zed-kernel/src/num.rs:961` | missing |
| `core::cmp::impls::<u64 as PartialEq<Self>>::eq` | 231 | 22 | `crates/zed-kernel/src/eval.rs:404` | `a == b` |
| `core::cmp::impls::<u64 as PartialEq<Self>>::ne` | 84 | 11 | `crates/zed-kernel/src/exact.rs:59` | `a != b` |
| `core::cmp::impls::<u64 as PartialOrd<Self>>::ge` | 39 | 6 | `crates/zed-kernel/src/num/bound.rs:124` | `a >= b` |
| `core::cmp::impls::<u64 as PartialOrd<Self>>::gt` | 45 | 7 | `crates/zed-kernel/src/num.rs:620` | `a > b` |
| `core::cmp::impls::<u64 as PartialOrd<Self>>::le` | 51 | 6 | `crates/zed-kernel/src/num/bound.rs:43` | `a <= b` |
| `core::cmp::impls::<u64 as PartialOrd<Self>>::lt` | 54 | 7 | `crates/zed-kernel/src/eval.rs:1382` | `a < b` |
| `core::cmp::impls::<u8 as Ord>::cmp` | 6 | 5 | `crates/zed-kernel/src/types/bdd.rs:1695` | missing |
| `core::cmp::impls::<u8 as PartialEq<Self>>::eq` | 141 | 13 | `crates/zed-kernel/src/types.rs:1001` | `a == b` |
| `core::cmp::impls::<u8 as PartialEq<Self>>::ne` | 84 | 8 | `crates/zed-kernel/src/types.rs:953` | `a != b` |
| `core::cmp::impls::<u8 as PartialOrd<Self>>::ge` | 9 | 2 | `crates/zed-kernel/src/text.rs:221` | `a >= b` |
| `core::cmp::impls::<u8 as PartialOrd<Self>>::gt` | 12 | 1 | `crates/zed-kernel/src/text.rs:203` | `a > b` |
| `core::cmp::impls::<u8 as PartialOrd<Self>>::le` | 3 | 1 | `crates/zedc/src/zir/binary.rs:396` | `a <= b` |
| `core::cmp::impls::<u8 as PartialOrd<Self>>::lt` | 9 | 2 | `crates/zedc/src/check/mod.rs:1719` | `a < b` |
| `core::cmp::impls::<usize as Ord>::clamp` | 1 | 1 | `crates/zedc/src/run.rs:427` | `min(max(x, a), b)` |
| `core::cmp::impls::<usize as Ord>::cmp` | 9 | 5 | `crates/zed-kernel/src/types/bdd.rs:1809` | missing |
| `core::cmp::impls::<usize as PartialEq<Self>>::eq` | 1053 | 65 | `crates/zed-kernel/src/bits.rs:118` | `a == b` |
| `core::cmp::impls::<usize as PartialEq<Self>>::ne` | 321 | 37 | `crates/zed-kernel/src/bits.rs:170` | `a != b` |
| `core::cmp::impls::<usize as PartialOrd<Self>>::ge` | 132 | 27 | `crates/zed-kernel/src/eval.rs:1194` | `a >= b` |
| `core::cmp::impls::<usize as PartialOrd<Self>>::gt` | 438 | 44 | `crates/zed-kernel/src/deep.rs:462` | `a > b` |
| `core::cmp::impls::<usize as PartialOrd<Self>>::le` | 183 | 24 | `crates/zed-kernel/src/num.rs:1009` | `a <= b` |
| `core::cmp::impls::<usize as PartialOrd<Self>>::lt` | 371 | 43 | `crates/zed-kernel/src/deep.rs:495` | `a < b` |
| `core::convert::<T as Into<U>>::into` | 431 | 56 | `crates/zed-kernel/src/eval.rs:232` | `x` |
| `core::convert::<T as TryInto<U>>::try_into` | 7 | 3 | `crates/zedc/src/elab/walk.rs:1398` | missing |
| `core::convert::AsRef::as_ref` | 1 | 1 | `crates/zedc/src/run.rs:875` | `x` |
| `core::convert::From::from` | 2 | 1 | `crates/zedc/src/store/presburger.rs:4533` | missing |
| `core::convert::Into::into` | 22 | 12 | `crates/zed-kernel/src/eval.rs:181` | `x` |
| `core::convert::num::<f64 as From<u8>>::from` | 2 | 1 | `crates/zed-kernel/src/types/empty.rs:652` | `f64(a)` |
| `core::convert::num::<i128 as From<bool>>::from` | 1 | 1 | `crates/zedc/src/check/widen.rs:827` | `if a { 1 } else { 0 }` |
| `core::convert::num::<i128 as From<i64>>::from` | 13 | 5 | `crates/zed-kernel/src/bits.rs:202` | `int(a)` |
| `core::convert::num::<i128 as From<u64>>::from` | 9 | 3 | `crates/zed-kernel/src/types/empty.rs:770` | `int(a)` |
| `core::convert::num::<i128 as TryFrom<u128>>::try_from` | 3 | 2 | `crates/zedc/src/check/widen.rs:437` | missing |
| `core::convert::num::<i32 as From<bool>>::from` | 1 | 1 | `crates/zedc/src/store/int.rs:417` | `if a { 1 } else { 0 }` |
| `core::convert::num::<i32 as From<u8>>::from` | 1 | 1 | `crates/zed-native/src/exe.rs:138` | `int(a)` |
| `core::convert::num::<i64 as From<bool>>::from` | 5 | 3 | `crates/zed-native/src/hooks.rs:595` | `if a { 1 } else { 0 }` |
| `core::convert::num::<i64 as From<i32>>::from` | 1 | 1 | `crates/zedc/src/store/int.rs:1611` | `int(a)` |
| `core::convert::num::<i64 as From<u32>>::from` | 8 | 5 | `crates/zed-kernel/src/bits.rs:180` | `int(a)` |
| `core::convert::num::<i64 as From<u8>>::from` | 1 | 1 | `crates/zed-kernel/src/words.rs:158` | `int(a)` |
| `core::convert::num::<i64 as TryFrom<i128>>::try_from` | 14 | 5 | `crates/zed-kernel/src/bits.rs:204` | missing |
| `core::convert::num::<i64 as TryFrom<u64>>::try_from` | 1 | 1 | `crates/zedc/src/check/widen.rs:798` | missing |
| `core::convert::num::<u128 as From<u32>>::from` | 1 | 1 | `crates/zedc/src/store/negsssp.rs:352` | `int(a)` |
| `core::convert::num::<u128 as From<u64>>::from` | 23 | 5 | `crates/zed-kernel/src/num.rs:919` | `int(a)` |
| `core::convert::num::<u32 as From<bool>>::from` | 6 | 3 | `crates/zed-kernel/src/num.rs:908` | `if a { 1 } else { 0 }` |
| `core::convert::num::<u32 as TryFrom<i64>>::try_from` | 8 | 6 | `crates/zed-kernel/src/eval.rs:2070` | missing |
| `core::convert::num::<u32 as TryFrom<u128>>::try_from` | 1 | 1 | `crates/zedc/src/check/widen.rs:706` | missing |
| `core::convert::num::<u32 as TryFrom<u64>>::try_from` | 2 | 2 | `crates/zed-kernel/src/num.rs:1184` | missing |
| `core::convert::num::<u64 as From<bool>>::from` | 14 | 7 | `crates/zed-kernel/src/num.rs:887` | `if a { 1 } else { 0 }` |
| `core::convert::num::<u64 as From<u32>>::from` | 5 | 5 | `crates/zed-kernel/src/provenance.rs:50` | `int(a)` |
| `core::convert::num::<u64 as From<u8>>::from` | 2 | 1 | `crates/zed-kernel/src/types.rs:120` | `int(a)` |
| `core::convert::num::<u64 as TryFrom<i128>>::try_from` | 3 | 3 | `crates/zed-kernel/src/types/empty.rs:778` | missing |
| `core::convert::num::<u64 as TryFrom<u128>>::try_from` | 4 | 3 | `crates/zed-kernel/src/num.rs:924` | missing |
| `core::convert::num::<u8 as From<bool>>::from` | 13 | 6 | `crates/zed-kernel/src/types.rs:619` | `if a { 1 } else { 0 }` |
| `core::convert::num::<u8 as TryFrom<i64>>::try_from` | 1 | 1 | `crates/zed-kernel/src/words.rs:173` | missing |
| `core::convert::num::<usize as From<bool>>::from` | 25 | 17 | `crates/zed-kernel/src/types/bdd/list.rs:415` | `if a { 1 } else { 0 }` |
| `core::convert::num::<usize as From<u8>>::from` | 1 | 1 | `crates/zed-kernel/src/text.rs:128` | `int(a)` |
| `core::convert::num::ptr_try_from_impls::<i64 as TryFrom<usize>>::try_from` | 4 | 3 | `crates/zed-kernel/src/words.rs:117` | missing |
| `core::convert::num::ptr_try_from_impls::<u32 as TryFrom<usize>>::try_from` | 5 | 3 | `crates/zed-kernel/src/eval.rs:421` | missing |
| `core::convert::num::ptr_try_from_impls::<u64 as TryFrom<usize>>::try_from` | 1 | 1 | `crates/zed-kernel/src/num.rs:140` | missing |
| `core::convert::num::ptr_try_from_impls::<usize as TryFrom<i32>>::try_from` | 1 | 1 | `crates/zed-native/src/exe.rs:125` | missing |
| `core::convert::num::ptr_try_from_impls::<usize as TryFrom<i64>>::try_from` | 7 | 5 | `crates/zed-kernel/src/eval.rs:2275` | missing |
| `core::convert::num::ptr_try_from_impls::<usize as TryFrom<u128>>::try_from` | 1 | 1 | `crates/zed-kernel/src/words.rs:248` | missing |
| `core::convert::num::ptr_try_from_impls::<usize as TryFrom<u64>>::try_from` | 4 | 4 | `crates/zed-kernel/src/num/bound.rs:119` | missing |
| `core::default::Default::default` | 2 | 1 | `crates/zed-kernel/src/types/rec.rs:89` | missing |
| `core::f32::f32::from_bits` | 1 | 1 | `crates/zed-kernel/src/num.rs:908` | missing |
| `core::f64::f64::abs` | 3 | 2 | `crates/zed-kernel/src/words.rs:115` | `abs(a)` |
| `core::f64::f64::from_bits` | 5 | 4 | `crates/zed-kernel/src/exact.rs:65` | missing |
| `core::f64::f64::is_finite` | 2 | 1 | `crates/zedc/src/store/float.rs:63` | missing |
| `core::f64::f64::is_infinite` | 4 | 3 | `crates/zed-kernel/src/exact.rs:103` | missing |
| `core::f64::f64::is_nan` | 8 | 6 | `crates/zed-kernel/src/eval.rs:2125` | row STD-num |
| `core::f64::f64::is_sign_negative` | 3 | 3 | `crates/zed-kernel/src/eval.rs:2130` | missing |
| `core::f64::f64::to_bits` | 11 | 9 | `crates/zed-kernel/src/bits.rs:50` | `f64Bits(x)` |
| `core::f64::f64::total_cmp` | 2 | 2 | `crates/zed-kernel/src/types/empty.rs:687` | missing |
| `core::ffi::c_str::CStr::from_ptr` | 1 | 1 | `crates/zed-native/src/exe.rs:131` | missing |
| `core::ffi::c_str::CStr::to_bytes` | 1 | 1 | `crates/zed-native/src/exe.rs:131` | missing |
| `core::fmt::<[T] as Debug>::fmt` | 1 | 1 | `crates/zed-kernel/src/value.rs:156` | missing |
| `core::fmt::<str as Debug>::fmt` | 1 | 1 | `crates/zed-kernel/src/text.rs:387` | missing |
| `core::fmt::Formatter<'a>::debug_list` | 1 | 1 | `crates/zedc/src/check/ty.rs:244` | missing |
| `core::fmt::Formatter<'a>::pad` | 1 | 1 | `crates/zed-kernel/src/text.rs:395` | missing |
| `core::fmt::Formatter<'a>::precision` | 1 | 1 | `crates/zed-kernel/src/text.rs:394` | missing |
| `core::fmt::Formatter<'a>::width` | 1 | 1 | `crates/zed-kernel/src/text.rs:394` | missing |
| `core::fmt::Formatter<'a>::write_str` | 52 | 20 | `crates/zed-kernel/src/deep.rs:514` | missing |
| `core::fmt::Write::write_str` | 1 | 1 | `crates/zed-kernel/src/print.rs:742` | missing |
| `core::fmt::builders::DebugList<'a, 'b>::entries` | 1 | 1 | `crates/zedc/src/check/ty.rs:244` | missing |
| `core::fmt::builders::DebugList<'a, 'b>::finish` | 1 | 1 | `crates/zedc/src/check/ty.rs:244` | missing |
| `core::fmt::write` | 4 | 2 | `crates/zed-kernel/src/words.rs:233` | missing |
| `core::future::future::Future::poll` | 377 | 3 | `crates/zed-kernel/src/frames.rs:51` | missing |
| `core::hash::<BuildHasherDefault<H> as Default>::default` | 2 | 1 | `crates/zedc/src/check/ty.rs:102` | missing |
| `core::hash::BuildHasher::hash_one` | 2 | 1 | `crates/zedc/src/check/ty.rs:102` | missing |
| `core::hash::Hasher::write` | 3 | 1 | `crates/zed-kernel/src/text.rs:367` | missing |
| `core::hash::Hasher::write_u64` | 7 | 3 | `crates/zed-kernel/src/provenance.rs:154` | missing |
| `core::hash::Hasher::write_u8` | 2 | 2 | `crates/zed-kernel/src/text.rs:381` | missing |
| `core::hash::impls::<(T, B) as Hash>::hash` | 1 | 1 | `crates/zedc/src/elab.rs:357` | missing |
| `core::hash::impls::<*const T as Hash>::hash` | 1 | 1 | `crates/zedc/src/store/presburger/deep.rs:111` | missing |
| `core::hash::impls::<i128 as Hash>::hash` | 1 | 1 | `crates/zedc/src/store/int.rs:2527` | missing |
| `core::hash::impls::<i64 as Hash>::hash` | 1 | 1 | `crates/zedc/src/store/int.rs:2526` | missing |
| `core::hash::impls::<i8 as Hash>::hash` | 1 | 1 | `crates/zedc/src/store/int.rs:2528` | missing |
| `core::hash::impls::<u64 as Hash>::hash` | 1 | 1 | `crates/zed-kernel/src/types.rs:80` | missing |
| `core::hint::black_box` | 2 | 2 | `crates/zed-kernel/src/types/bdd.rs:2197` | row L6.13 |
| `core::intrinsics::transmute` | 1 | 1 | `crates/zed-native/src/lib.rs:169` | row L6.13 |
| `core::io::error::<ErrorKind as PartialEq<Self>>::eq` | 9 | 3 | `crates/zed-native/src/link.rs:141` | `a == b` |
| `core::io::error::Error::kind` | 3 | 3 | `crates/zed-native/src/link.rs:141` | missing |
| `core::io::util::sink` | 1 | 1 | `crates/zed-kernel/src/text.rs:735` | missing |
| `core::io::write::Write::write_all` | 3 | 2 | `crates/zed-native/src/link.rs:126` | missing |
| `core::iter::adapters::chain::<Chain<A, B> as Iterator>::count` | 6 | 2 | `crates/zed-kernel/src/types/rec.rs:170` | `xs.count` |
| `core::iter::adapters::chain::<Chain<A, B> as Iterator>::find` | 1 | 1 | `crates/zedc/src/zir/mod.rs:638` | `xs.where(p).first` |
| `core::iter::adapters::chain::<Chain<A, B> as Iterator>::fold` | 1 | 1 | `crates/zed-kernel/src/types/rec.rs:197` | `xs.foldl(z, f)` |
| `core::iter::adapters::copied::<Copied<I> as Iterator>::next` | 1 | 1 | `crates/zedc/src/stage.rs:247` | row STD-seq |
| `core::iter::adapters::filter::<Filter<I, P> as Clone>::clone` | 1 | 1 | `crates/zedc/src/zir/memory.rs:670` | `x` |
| `core::iter::adapters::filter::<Filter<I, P> as DoubleEndedIterator>::next_back` | 1 | 1 | `crates/zedc/src/zir/memory.rs:676` | missing |
| `core::iter::adapters::filter::<Filter<I, P> as Iterator>::count` | 13 | 8 | `crates/zed-kernel/src/types/bes.rs:646` | `xs.count` |
| `core::iter::adapters::filter::<Filter<I, P> as Iterator>::fold` | 6 | 4 | `crates/zedc/src/check/mod.rs:2218` | `xs.foldl(z, f)` |
| `core::iter::adapters::filter::<Filter<I, P> as Iterator>::next` | 12 | 5 | `crates/zed-kernel/src/types/bdd.rs:887` | row STD-seq |
| `core::iter::adapters::flatten::<FlatMap<I, U, F> as Iterator>::fold` | 2 | 2 | `crates/zedc/src/check/widen.rs:778` | `xs.foldl(z, f)` |
| `core::iter::adapters::flatten::<Flatten<I> as Iterator>::fold` | 1 | 1 | `crates/zedc/src/store/presburger.rs:2303` | `xs.foldl(z, f)` |
| `core::iter::adapters::flatten::<Flatten<I> as Iterator>::next` | 4 | 2 | `crates/zedc/src/store/conjuncts.rs:735` | row STD-seq |
| `core::iter::adapters::map::<Map<I, F> as Clone>::clone` | 1 | 1 | `crates/zed-kernel/src/types/empty.rs:2607` | `x` |
| `core::iter::adapters::map::<Map<I, F> as Iterator>::fold` | 4 | 3 | `crates/zedc/src/store/cell.rs:180` | `xs.foldl(z, f)` |
| `core::iter::adapters::map::<Map<I, F> as Iterator>::next` | 4 | 3 | `crates/zedc/src/check/mod.rs:6035` | row STD-seq |
| `core::iter::adapters::peekable::<Peekable<I> as Iterator>::next` | 21 | 4 | `crates/zedc/src/lex/name.rs:23` | row STD-seq |
| `core::iter::adapters::peekable::Peekable<I>::next_if` | 5 | 3 | `crates/zedc/src/ast/mod.rs:958` | missing |
| `core::iter::adapters::peekable::Peekable<I>::peek` | 12 | 5 | `crates/zedc/src/lex/name.rs:25` | `xs.first` |
| `core::iter::adapters::rev::<Rev<I> as ExactSizeIterator>::len` | 1 | 1 | `crates/zed-kernel/src/num.rs:1229` | `xs.count` |
| `core::iter::adapters::rev::<Rev<I> as Iterator>::find` | 1 | 1 | `crates/zed-kernel/src/exact.rs:59` | `xs.where(p).last` |
| `core::iter::adapters::rev::<Rev<I> as Iterator>::fold` | 17 | 10 | `crates/zed-kernel/src/num.rs:1191` | `xs.foldr((x, acc) -> f(acc, x), z)` |
| `core::iter::adapters::zip::<Zip<A, B> as Iterator>::fold` | 3 | 3 | `crates/zed-kernel/src/types/rec.rs:600` | `xs.foldl(z, f)` |
| `core::iter::sources::from_fn::from_fn` | 2 | 2 | `crates/zed-kernel/src/num.rs:1086` | missing |
| `core::iter::sources::once::once` | 15 | 7 | `crates/zed-kernel/src/types/bdd.rs:142` | missing |
| `core::iter::sources::repeat::repeat` | 1 | 1 | `crates/zed-kernel/src/eval.rs:1316` | missing |
| `core::iter::sources::repeat_n::repeat_n` | 3 | 2 | `crates/zed-kernel/src/num/factor.rs:14` | missing |
| `core::iter::traits::collect::<I as IntoIterator>::into_iter` | 1 | 1 | `crates/zedc/src/elab.rs:1070` | row STD-seq |
| `core::iter::traits::collect::IntoIterator::into_iter` | 20 | 10 | `crates/zed-kernel/src/family.rs:223` | row STD-seq |
| `core::iter::traits::exact_size::ExactSizeIterator::len` | 2 | 1 | `crates/zed-kernel/src/types/empty.rs:1836` | `xs.count` |
| `core::iter::traits::iterator::Iterator::all` | 71 | 27 | `crates/zed-kernel/src/deep.rs:487` | `xs.all(p)` |
| `core::iter::traits::iterator::Iterator::any` | 61 | 23 | `crates/zed-kernel/src/exact.rs:52` | `xs.any(p)` |
| `core::iter::traits::iterator::Iterator::by_ref` | 5 | 4 | `crates/zed-kernel/src/num.rs:1238` | `x` |
| `core::iter::traits::iterator::Iterator::chain` | 88 | 32 | `crates/zed-kernel/src/eval.rs:1316` | `xs ++ ys` |
| `core::iter::traits::iterator::Iterator::cloned` | 104 | 20 | `crates/zed-kernel/src/eval.rs:440` | `x` |
| `core::iter::traits::iterator::Iterator::cmp` | 4 | 3 | `crates/zed-kernel/src/exact.rs:44` | missing |
| `core::iter::traits::iterator::Iterator::collect` | 1023 | 79 | `crates/zed-kernel/src/bits.rs:60` | `x` |
| `core::iter::traits::iterator::Iterator::copied` | 56 | 22 | `crates/zed-kernel/src/types.rs:1798` | `x` |
| `core::iter::traits::iterator::Iterator::count` | 7 | 7 | `crates/zedc/src/canon/mod.rs:108` | `xs.count` |
| `core::iter::traits::iterator::Iterator::enumerate` | 238 | 52 | `crates/zed-kernel/src/bits.rs:117` | row STD-seq |
| `core::iter::traits::iterator::Iterator::filter` | 232 | 41 | `crates/zed-kernel/src/eval.rs:1452` | `xs.where(p)` |
| `core::iter::traits::iterator::Iterator::filter_map` | 101 | 26 | `crates/zed-kernel/src/types/empty.rs:567` | row STD-seq |
| `core::iter::traits::iterator::Iterator::find` | 37 | 20 | `crates/zed-kernel/src/types/empty.rs:568` | `xs.where(p).first` |
| `core::iter::traits::iterator::Iterator::find_map` | 5 | 4 | `crates/zed-kernel/src/types/empty.rs:2157` | row STD-seq |
| `core::iter::traits::iterator::Iterator::flat_map` | 71 | 23 | `crates/zed-kernel/src/provenance.rs:425` | `xs.flatMap(f)` |
| `core::iter::traits::iterator::Iterator::flatten` | 70 | 17 | `crates/zed-kernel/src/eval.rs:815` | `xs.flatMap(x -> x)` |
| `core::iter::traits::iterator::Iterator::fold` | 9 | 5 | `crates/zed-kernel/src/types.rs:144` | `xs.foldl(z, f)` |
| `core::iter::traits::iterator::Iterator::for_each` | 22 | 9 | `crates/zed-kernel/src/provenance.rs:472` | missing |
| `core::iter::traits::iterator::Iterator::last` | 1 | 1 | `crates/zedc/src/store/affine.rs:439` | `xs.last` |
| `core::iter::traits::iterator::Iterator::map` | 983 | 81 | `crates/zed-kernel/src/bits.rs:60` | `xs.map(f)` |
| `core::iter::traits::iterator::Iterator::max` | 18 | 12 | `crates/zed-kernel/src/num/bound.rs:155` | `xs.maxBy(x -> x).last` |
| `core::iter::traits::iterator::Iterator::max_by_key` | 6 | 6 | `crates/zed-kernel/src/value.rs:386` | `xs.maxBy(f).last` |
| `core::iter::traits::iterator::Iterator::min` | 15 | 9 | `crates/zed-kernel/src/types/bes.rs:754` | `xs.minBy(x -> x).first` |
| `core::iter::traits::iterator::Iterator::min_by` | 1 | 1 | `crates/zed-kernel/src/types/empty.rs:687` | `xs.sort(by: f).first` |
| `core::iter::traits::iterator::Iterator::min_by_key` | 11 | 6 | `crates/zed-kernel/src/types/empty.rs:1677` | `xs.minBy(f).first` |
| `core::iter::traits::iterator::Iterator::next` | 1 | 1 | `crates/zedc/src/canon/binders.rs:701` | row STD-seq |
| `core::iter::traits::iterator::Iterator::nth` | 3 | 3 | `crates/zed-kernel/src/provenance.rs:649` | `xs.drop(n).first` |
| `core::iter::traits::iterator::Iterator::partition` | 3 | 2 | `crates/zedc/src/store/presburger.rs:3371` | missing |
| `core::iter::traits::iterator::Iterator::peekable` | 11 | 7 | `crates/zedc/src/ast/mod.rs:957` | missing |
| `core::iter::traits::iterator::Iterator::position` | 3 | 2 | `crates/zedc/src/canon/mod.rs:101` | `xs.find(p)` |
| `core::iter::traits::iterator::Iterator::product` | 4 | 4 | `crates/zed-kernel/src/types/empty.rs:676` | `xs.foldl(1, (a, b) -> a * b)` |
| `core::iter::traits::iterator::Iterator::reduce` | 5 | 4 | `crates/zedc/src/check/ty.rs:2388` | `xs.reduce(f)` |
| `core::iter::traits::iterator::Iterator::rev` | 223 | 52 | `crates/zed-kernel/src/deep.rs:460` | row STD-seq |
| `core::iter::traits::iterator::Iterator::skip` | 7 | 7 | `crates/zed-native/src/hooks.rs:644` | `xs.drop(n)` |
| `core::iter::traits::iterator::Iterator::step_by` | 5 | 3 | `crates/zedc/src/ast/stmts.rs:423` | missing |
| `core::iter::traits::iterator::Iterator::sum` | 12 | 8 | `crates/zed-kernel/src/num.rs:619` | `sum(xs)` |
| `core::iter::traits::iterator::Iterator::take` | 2 | 2 | `crates/zed-kernel/src/num.rs:1238` | `xs.take(n)` |
| `core::iter::traits::iterator::Iterator::take_while` | 10 | 7 | `crates/zedc/src/check/mod.rs:2603` | `xs.takeWhile(p)` |
| `core::iter::traits::iterator::Iterator::try_fold` | 3 | 3 | `crates/zedc/src/check/mod.rs:5438` | missing |
| `core::iter::traits::iterator::Iterator::try_for_each` | 6 | 5 | `crates/zed-kernel/src/provenance.rs:165` | missing |
| `core::iter::traits::iterator::Iterator::unzip` | 4 | 4 | `crates/zed-kernel/src/types.rs:771` | missing |
| `core::iter::traits::iterator::Iterator::zip` | 143 | 37 | `crates/zed-kernel/src/bits.rs:117` | `xs.take(ys.count).zip(ys.take(xs.count))` |
| `core::macros::assert_eq!` | 337 | 33 | `crates/zed-kernel/src/bits.rs:316` | row S.1d |
| `core::macros::assert_ne!` | 8 | 6 | `crates/zed-kernel/src/text.rs:546` | row S.1d |
| `core::macros::builtin::assert!` | 126 | 27 | `crates/zed-kernel/src/exact.rs:171` | row S.1d |
| `core::macros::builtin::cfg!` | 2 | 2 | `crates/zed-kernel/src/address.rs:12` | missing |
| `core::macros::builtin::concat!` | 1 | 1 | `crates/zed-native/src/link.rs:212` | missing |
| `core::macros::builtin::env!` | 4 | 3 | `crates/zed-native/src/link.rs:212` | missing |
| `core::macros::builtin::format_args!` | 6 | 2 | `crates/zed-kernel/src/words.rs:253` | missing |
| `core::macros::builtin::include!` | 1 | 1 | `crates/zed-native/src/link.rs:212` | missing |
| `core::macros::builtin::include_str!` | 2 | 1 | `crates/zedc/src/parse/mod.rs:37` | missing |
| `core::macros::builtin::line!` | 4 | 1 | `crates/zed-kernel/src/text.rs:711` | missing |
| `core::macros::debug_assert!` | 18 | 10 | `crates/zed-kernel/src/provenance.rs:329` | row S.1d |
| `core::macros::debug_assert_eq!` | 2 | 2 | `crates/zed-native/src/hooks.rs:63` | row S.1d |
| `core::macros::matches!` | 263 | 55 | `crates/zed-kernel/src/bits.rs:29` | missing |
| `core::macros::todo!` | 2 | 1 | `crates/zed-kernel/src/text.rs:428` | row S.1d |
| `core::macros::unreachable!` | 211 | 48 | `crates/zed-kernel/src/eval.rs:398` | row S.1d |
| `core::macros::write!` | 176 | 35 | `crates/zed-kernel/src/deep.rs:505` | missing |
| `core::macros::writeln!` | 30 | 7 | `crates/zed-native/src/exe.rs:149` | missing |
| `core::mem::<Discriminant<T> as PartialEq<Self>>::eq` | 3 | 1 | `crates/zed-kernel/src/eval.rs:2233` | missing |
| `core::mem::discriminant` | 7 | 4 | `crates/zed-kernel/src/eval.rs:2233` | missing |
| `core::mem::drop` | 17 | 10 | `crates/zed-kernel/src/deep.rs:79` | row L6.13 |
| `core::mem::manually_drop::<ManuallyDrop<T> as DerefMut>::deref_mut` | 1 | 1 | `crates/zed-native/src/lib.rs:159` | `x` |
| `core::mem::manually_drop::ManuallyDrop<T>::into_inner` | 1 | 1 | `crates/zed-kernel/src/frames.rs:85` | `x` |
| `core::mem::manually_drop::ManuallyDrop<T>::new` | 3 | 2 | `crates/zed-kernel/src/frames.rs:37` | missing |
| `core::mem::manually_drop::ManuallyDrop<T>::take` | 1 | 1 | `crates/zed-native/src/lib.rs:109` | row L6.13 |
| `core::mem::replace` | 64 | 27 | `crates/zed-kernel/src/deep.rs:270` | row L6.13 |
| `core::mem::size_of` | 1 | 1 | `crates/zed-kernel/src/text.rs:746` | row L6.13 |
| `core::mem::size_of_val` | 1 | 1 | `crates/zed-kernel/src/frames.rs:207` | row L6.13 |
| `core::mem::swap` | 6 | 2 | `crates/zedc/src/check/mod.rs:1755` | row L6.13 |
| `core::mem::take` | 144 | 38 | `crates/zed-kernel/src/deep.rs:298` | row L6.13 |
| `core::num::i128::abs` | 4 | 2 | `crates/zedc/src/store/preimage.rs:803` | `abs(a)` |
| `core::num::i128::checked_add` | 8 | 2 | `crates/zedc/src/store/int.rs:203` | missing |
| `core::num::i128::checked_mul` | 14 | 3 | `crates/zedc/src/store/int.rs:233` | missing |
| `core::num::i128::checked_neg` | 3 | 2 | `crates/zedc/src/store/int.rs:246` | missing |
| `core::num::i128::checked_pow` | 2 | 2 | `crates/zedc/src/check/widen.rs:830` | missing |
| `core::num::i128::checked_sub` | 5 | 2 | `crates/zedc/src/store/int.rs:216` | missing |
| `core::num::i128::checked_sub_unsigned` | 1 | 1 | `crates/zedc/src/store/int.rs:1947` | missing |
| `core::num::i128::div_euclid` | 4 | 3 | `crates/zedc/src/check/widen.rs:776` | `a div b` |
| `core::num::i128::rem_euclid` | 4 | 3 | `crates/zed-kernel/src/types/empty.rs:778` | `a mod b` |
| `core::num::i128::unsigned_abs` | 10 | 2 | `crates/zedc/src/store/int.rs:162` | `abs(a)` |
| `core::num::i64::checked_abs` | 1 | 1 | `crates/zed-kernel/src/words.rs:98` | missing |
| `core::num::i64::checked_add` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2065` | missing |
| `core::num::i64::checked_div_euclid` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2068` | missing |
| `core::num::i64::checked_mul` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2067` | missing |
| `core::num::i64::checked_neg` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2190` | missing |
| `core::num::i64::checked_pow` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2070` | missing |
| `core::num::i64::checked_rem_euclid` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2069` | missing |
| `core::num::i64::checked_sub` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2066` | missing |
| `core::num::i64::count_ones` | 1 | 1 | `crates/zed-kernel/src/bits.rs:197` | `popCount(a)` |
| `core::num::i64::div_euclid` | 1 | 1 | `crates/zedc/src/store/int.rs:179` | `a div b` |
| `core::num::i64::leading_zeros` | 1 | 1 | `crates/zed-kernel/src/bits.rs:180` | `leadingZeros(a, width: 64)` |
| `core::num::i64::rem_euclid` | 5 | 2 | `crates/zedc/src/check/widen.rs:793` | `a mod b` |
| `core::num::i64::saturating_add` | 1 | 1 | `crates/zedc/src/check/widen.rs:811` | `min(max(a + b, -(2 ** 63)), 2 ** 63 - 1)` |
| `core::num::i64::signum` | 1 | 1 | `crates/zedc/src/store/int.rs:1811` | `if a > 0 { 1 } else if a < 0 { -1 } else { 0 }` |
| `core::num::i64::trailing_zeros` | 2 | 2 | `crates/zed-kernel/src/bits.rs:200` | `trailingZeros(a, width: 64)` |
| `core::num::i64::unsigned_abs` | 17 | 5 | `crates/zed-kernel/src/num/bound.rs:109` | `abs(a)` |
| `core::num::u128::checked_add` | 1 | 1 | `crates/zed-kernel/src/words.rs:273` | missing |
| `core::num::u128::checked_pow` | 1 | 1 | `crates/zedc/src/store/int.rs:1945` | missing |
| `core::num::u128::from_str_radix` | 1 | 1 | `crates/zedc/src/check/widen.rs:684` | row STD-num |
| `core::num::u128::is_power_of_two` | 1 | 1 | `crates/zedc/src/check/widen.rs:693` | `popCount(a) == 1` |
| `core::num::u128::saturating_add` | 2 | 1 | `crates/zedc/src/store/preimage.rs:4511` | `min(a + b, 2 ** 128 - 1)` |
| `core::num::u128::saturating_mul` | 4 | 1 | `crates/zedc/src/store/preimage.rs:4511` | `min(a * b, 2 ** 128 - 1)` |
| `core::num::u128::saturating_sub` | 3 | 1 | `crates/zed-kernel/src/words.rs:308` | `max(a - b, 0)` |
| `core::num::u128::trailing_zeros` | 1 | 1 | `crates/zedc/src/check/widen.rs:696` | `trailingZeros(a, width: 128)` |
| `core::num::u32::checked_add` | 1 | 1 | `crates/zedc/src/store/preimage.rs:1046` | missing |
| `core::num::u32::from_le_bytes` | 1 | 1 | `crates/zedc/src/zir/binary.rs:345` | row STD-num |
| `core::num::u32::from_str_radix` | 3 | 2 | `crates/zedc/src/lex/string.rs:206` | row STD-num |
| `core::num::u32::ilog2` | 1 | 1 | `crates/zed-kernel/src/value.rs:453` | `31 - leadingZeros(a, width: 32)` |
| `core::num::u32::is_power_of_two` | 1 | 1 | `crates/zed-kernel/src/value.rs:453` | `popCount(a) == 1` |
| `core::num::u32::leading_zeros` | 3 | 2 | `crates/zedc/src/stage.rs:498` | `leadingZeros(a, width: 32)` |
| `core::num::u32::to_le_bytes` | 6 | 3 | `crates/zedc/src/canon/mod.rs:200` | row STD-num |
| `core::num::u64::abs_diff` | 2 | 1 | `crates/zed-kernel/src/num/factor.rs:99` | `abs(a - b)` |
| `core::num::u64::checked_mul` | 1 | 1 | `crates/zed-kernel/src/types/empty.rs:573` | missing |
| `core::num::u64::div_ceil` | 5 | 2 | `crates/zedc/src/cost.rs:67` | `-((-a) div b)` |
| `core::num::u64::from_le_bytes` | 2 | 2 | `crates/zed-native/src/exe.rs:54` | row STD-num |
| `core::num::u64::ilog2` | 3 | 2 | `crates/zed-kernel/src/num.rs:1143` | `63 - leadingZeros(a, width: 64)` |
| `core::num::u64::is_multiple_of` | 6 | 3 | `crates/zed-kernel/src/num/factor.rs:12` | `a mod b == 0` |
| `core::num::u64::is_power_of_two` | 2 | 2 | `crates/zed-kernel/src/num.rs:1143` | `popCount(a) == 1` |
| `core::num::u64::leading_zeros` | 5 | 4 | `crates/zed-kernel/src/exact.rs:61` | `leadingZeros(a, width: 64)` |
| `core::num::u64::overflowing_sub` | 2 | 1 | `crates/zed-kernel/src/exact.rs:35` | `((a - b) mod 2 ** 64, a < b)` |
| `core::num::u64::rotate_left` | 3 | 3 | `crates/zed-kernel/src/provenance.rs:50` | `rotl(a, n, width: 64)` |
| `core::num::u64::saturating_add` | 9 | 1 | `crates/zedc/src/cost.rs:67` | `min(a + b, 2 ** 64 - 1)` |
| `core::num::u64::saturating_mul` | 3 | 2 | `crates/zedc/src/cost.rs:67` | `min(a * b, 2 ** 64 - 1)` |
| `core::num::u64::to_le_bytes` | 13 | 8 | `crates/zed-native/src/exe.rs:42` | row STD-num |
| `core::num::u64::trailing_zeros` | 3 | 2 | `crates/zed-kernel/src/num/factor.rs:13` | `trailingZeros(a, width: 64)` |
| `core::num::u64::wrapping_add` | 7 | 4 | `crates/zed-kernel/src/eval.rs:1980` | `(a + b) mod 2 ** 64` |
| `core::num::u64::wrapping_mul` | 13 | 5 | `crates/zed-kernel/src/eval.rs:1982` | `(a * b) mod 2 ** 64` |
| `core::num::u64::wrapping_sub` | 2 | 1 | `crates/zed-kernel/src/types.rs:1138` | `(a - b) mod 2 ** 64` |
| `core::num::u8::abs_diff` | 2 | 1 | `crates/zed-kernel/src/text.rs:188` | `abs(a - b)` |
| `core::num::u8::count_ones` | 4 | 1 | `crates/zedc/src/check/mod.rs:2292` | `popCount(a)` |
| `core::num::u8::is_ascii_digit` | 11 | 7 | `crates/zed-kernel/src/num.rs:120` | missing |
| `core::num::u8::is_ascii_hexdigit` | 1 | 1 | `crates/zedc/src/lex/string.rs:202` | missing |
| `core::num::usize::checked_add` | 1 | 1 | `crates/zed-kernel/src/text.rs:85` | missing |
| `core::num::usize::checked_mul` | 1 | 1 | `crates/zedc/src/zir/binary.rs:553` | missing |
| `core::num::usize::checked_sub` | 13 | 7 | `crates/zed-kernel/src/print.rs:751` | missing |
| `core::num::usize::div_ceil` | 1 | 1 | `crates/zedc/src/store/revision.rs:364` | `-((-a) div b)` |
| `core::num::usize::ilog2` | 1 | 1 | `crates/zed-kernel/src/num.rs:1020` | `63 - leadingZeros(a, width: 64)` |
| `core::num::usize::isolate_lowest_one` | 2 | 1 | `crates/zedc/src/store/preimage.rs:728` | row STD-num |
| `core::num::usize::saturating_add` | 1 | 1 | `crates/zedc/src/store/conjuncts.rs:891` | `min(a + b, 2 ** 64 - 1)` |
| `core::num::usize::saturating_sub` | 6 | 6 | `crates/zed-kernel/src/print.rs:827` | `max(a - b, 0)` |
| `core::num::usize::trailing_zeros` | 2 | 2 | `crates/zed-kernel/src/exact.rs:195` | `trailingZeros(a, width: 64)` |
| `core::num::usize::wrapping_sub` | 1 | 1 | `crates/zedc/src/canon/binders.rs:416` | `(a - b) mod 2 ** 64` |
| `core::ops::arith::<&u32 as Add<u32>>::add` | 3 | 1 | `crates/zedc/src/store/presburger.rs:6224` | `a + b` |
| `core::ops::arith::<&u64 as Mul<Self>>::mul` | 3 | 1 | `crates/zedc/src/store/int.rs:1587` | `a * b` |
| `core::ops::arith::<&usize as Add<usize>>::add` | 7 | 3 | `crates/zedc/src/store/presburger.rs:5491` | `a + b` |
| `core::ops::arith::<f64 as Add<Self>>::add` | 6 | 2 | `crates/zed-kernel/src/eval.rs:2209` | `a + b` |
| `core::ops::arith::<f64 as Div<Self>>::div` | 6 | 2 | `crates/zed-kernel/src/eval.rs:2212` | `a / b` |
| `core::ops::arith::<f64 as Mul<Self>>::mul` | 6 | 2 | `crates/zed-kernel/src/eval.rs:2211` | `a * b` |
| `core::ops::arith::<f64 as Neg>::neg` | 3 | 2 | `crates/zed-kernel/src/eval.rs:2213` | `-a` |
| `core::ops::arith::<f64 as Sub<Self>>::sub` | 6 | 2 | `crates/zed-kernel/src/eval.rs:2210` | `a - b` |
| `core::ops::arith::<i128 as Add<Self>>::add` | 22 | 4 | `crates/zedc/src/check/widen.rs:749` | `a + b` |
| `core::ops::arith::<i128 as Div<Self>>::div` | 3 | 1 | `crates/zed-kernel/src/types/empty.rs:773` | `if (a < 0) != (b < 0) { -(abs(a) div abs(b)) } else { abs(a) div abs(b) }` |
| `core::ops::arith::<i128 as Mul<Self>>::mul` | 27 | 4 | `crates/zed-kernel/src/types/empty.rs:774` | `a * b` |
| `core::ops::arith::<i128 as Neg>::neg` | 19 | 4 | `crates/zedc/src/check/widen.rs:438` | `-a` |
| `core::ops::arith::<i128 as Rem<Self>>::rem` | 6 | 1 | `crates/zedc/src/store/preimage_ref.rs:3113` | `if a < 0 { -((-a) mod abs(b)) } else { a mod abs(b) }` |
| `core::ops::arith::<i128 as Sub<Self>>::sub` | 48 | 6 | `crates/zed-kernel/src/bits.rs:202` | `a - b` |
| `core::ops::arith::<i32 as Add<Self>>::add` | 13 | 2 | `crates/zed-kernel/src/num.rs:1565` | `a + b` |
| `core::ops::arith::<i32 as AddAssign<Self>>::add_assign` | 48 | 8 | `crates/zed-kernel/src/types/bdd.rs:1157` | `a + b` |
| `core::ops::arith::<i32 as Neg>::neg` | 23 | 9 | `crates/zed-kernel/src/num.rs:752` | `-a` |
| `core::ops::arith::<i32 as Sub<Self>>::sub` | 5 | 2 | `crates/zed-kernel/src/num.rs:1564` | `a - b` |
| `core::ops::arith::<i32 as SubAssign<Self>>::sub_assign` | 6 | 2 | `crates/zed-kernel/src/types/bdd.rs:1190` | `a - b` |
| `core::ops::arith::<i64 as Add<Self>>::add` | 18 | 4 | `crates/zed-kernel/src/num.rs:885` | `a + b` |
| `core::ops::arith::<i64 as AddAssign<&i64>>::add_assign` | 3 | 1 | `crates/zed-kernel/src/types/bdd/list.rs:299` | `a + b` |
| `core::ops::arith::<i64 as AddAssign<Self>>::add_assign` | 24 | 4 | `crates/zed-kernel/src/eval.rs:1269` | `a + b` |
| `core::ops::arith::<i64 as Neg>::neg` | 22 | 11 | `crates/zed-kernel/src/eval.rs:2093` | `-a` |
| `core::ops::arith::<i64 as Rem<Self>>::rem` | 9 | 2 | `crates/zed-kernel/src/bits.rs:215` | `if a < 0 { -((-a) mod abs(b)) } else { a mod abs(b) }` |
| `core::ops::arith::<i64 as Sub<Self>>::sub` | 24 | 7 | `crates/zed-kernel/src/bits.rs:198` | `a - b` |
| `core::ops::arith::<i64 as SubAssign<Self>>::sub_assign` | 12 | 2 | `crates/zed-kernel/src/num/bound.rs:363` | `a - b` |
| `core::ops::arith::<i8 as Mul<Self>>::mul` | 9 | 1 | `crates/zedc/src/store/revision.rs:189` | `a * b` |
| `core::ops::arith::<i8 as Neg>::neg` | 3 | 2 | `crates/zedc/src/store/int.rs:1813` | `-a` |
| `core::ops::arith::<isize as AddAssign<Self>>::add_assign` | 6 | 1 | `crates/zed-kernel/src/types/bdd.rs:408` | `a + b` |
| `core::ops::arith::<isize as Mul<Self>>::mul` | 3 | 1 | `crates/zedc/src/store/presburger.rs:4070` | `a * b` |
| `core::ops::arith::<isize as Sub<Self>>::sub` | 6 | 1 | `crates/zedc/src/store/presburger.rs:4069` | `a - b` |
| `core::ops::arith::<isize as SubAssign<Self>>::sub_assign` | 3 | 1 | `crates/zed-kernel/src/types/bdd.rs:409` | `a - b` |
| `core::ops::arith::<u128 as Add<Self>>::add` | 40 | 5 | `crates/zed-kernel/src/error.rs:215` | `a + b` |
| `core::ops::arith::<u128 as AddAssign<Self>>::add_assign` | 6 | 1 | `crates/zed-kernel/src/words.rs:225` | `a + b` |
| `core::ops::arith::<u128 as Mul<Self>>::mul` | 36 | 6 | `crates/zed-kernel/src/num.rs:919` | `a * b` |
| `core::ops::arith::<u128 as Rem<Self>>::rem` | 18 | 4 | `crates/zed-kernel/src/num.rs:1191` | `a mod b` |
| `core::ops::arith::<u128 as Sub<Self>>::sub` | 6 | 2 | `crates/zed-kernel/src/num.rs:923` | `a - b` |
| `core::ops::arith::<u32 as Add<Self>>::add` | 66 | 9 | `crates/zed-kernel/src/exact.rs:61` | `a + b` |
| `core::ops::arith::<u32 as AddAssign<Self>>::add_assign` | 66 | 9 | `crates/zed-kernel/src/exact.rs:81` | `a + b` |
| `core::ops::arith::<u32 as Div<Self>>::div` | 6 | 1 | `crates/zed-kernel/src/exact.rs:12` | `a div b` |
| `core::ops::arith::<u32 as Mul<Self>>::mul` | 3 | 1 | `crates/zed-kernel/src/exact.rs:61` | `a * b` |
| `core::ops::arith::<u32 as Rem<Self>>::rem` | 9 | 2 | `crates/zed-kernel/src/exact.rs:13` | `a mod b` |
| `core::ops::arith::<u32 as Sub<Self>>::sub` | 60 | 8 | `crates/zed-kernel/src/bits.rs:180` | `a - b` |
| `core::ops::arith::<u32 as SubAssign<Self>>::sub_assign` | 33 | 3 | `crates/zed-kernel/src/types/bdd/list.rs:327` | `a - b` |
| `core::ops::arith::<u64 as Add<Self>>::add` | 120 | 13 | `crates/zed-kernel/src/eval.rs:1990` | `a + b` |
| `core::ops::arith::<u64 as AddAssign<Self>>::add_assign` | 129 | 17 | `crates/zed-kernel/src/eval.rs:1657` | `a + b` |
| `core::ops::arith::<u64 as Div<Self>>::div` | 18 | 4 | `crates/zed-kernel/src/num/factor.rs:21` | `a div b` |
| `core::ops::arith::<u64 as DivAssign<Self>>::div_assign` | 3 | 1 | `crates/zed-kernel/src/types/empty.rs:495` | `a div b` |
| `core::ops::arith::<u64 as Mul<Self>>::mul` | 57 | 4 | `crates/zed-kernel/src/family.rs:50` | `a * b` |
| `core::ops::arith::<u64 as MulAssign<Self>>::mul_assign` | 30 | 4 | `crates/zed-kernel/src/num/bound.rs:220` | `a * b` |
| `core::ops::arith::<u64 as Rem<Self>>::rem` | 84 | 5 | `crates/zed-kernel/src/eval.rs:1990` | `a mod b` |
| `core::ops::arith::<u64 as RemAssign<Self>>::rem_assign` | 3 | 1 | `crates/zed-kernel/src/num/factor.rs:41` | `a mod b` |
| `core::ops::arith::<u64 as Sub<Self>>::sub` | 105 | 12 | `crates/zed-kernel/src/bits.rs:218` | `a - b` |
| `core::ops::arith::<u64 as SubAssign<Self>>::sub_assign` | 9 | 2 | `crates/zed-kernel/src/eval.rs:407` | `a - b` |
| `core::ops::arith::<u8 as Add<Self>>::add` | 33 | 3 | `crates/zed-kernel/src/text.rs:193` | `a + b` |
| `core::ops::arith::<u8 as AddAssign<Self>>::add_assign` | 6 | 2 | `crates/zed-kernel/src/types/bdd/list.rs:284` | `a + b` |
| `core::ops::arith::<u8 as Sub<Self>>::sub` | 9 | 2 | `crates/zedc/src/address.rs:20` | `a - b` |
| `core::ops::arith::<u8 as SubAssign<Self>>::sub_assign` | 3 | 1 | `crates/zed-kernel/src/types/bdd/list.rs:326` | `a - b` |
| `core::ops::arith::<usize as Add<&usize>>::add` | 9 | 3 | `crates/zedc/src/store/presburger.rs:5788` | `a + b` |
| `core::ops::arith::<usize as Add<Self>>::add` | 1310 | 68 | `crates/zed-kernel/src/deep.rs:495` | `a + b` |
| `core::ops::arith::<usize as AddAssign<Self>>::add_assign` | 753 | 56 | `crates/zed-kernel/src/eval.rs:902` | `a + b` |
| `core::ops::arith::<usize as Div<Self>>::div` | 60 | 11 | `crates/zed-kernel/src/exact.rs:196` | `a div b` |
| `core::ops::arith::<usize as Mul<&usize>>::mul` | 6 | 1 | `crates/zedc/src/store/utvpi.rs:65` | `a * b` |
| `core::ops::arith::<usize as Mul<Self>>::mul` | 183 | 14 | `crates/zed-kernel/src/num.rs:1234` | `a * b` |
| `core::ops::arith::<usize as MulAssign<Self>>::mul_assign` | 3 | 1 | `crates/zedc/src/store/presburger.rs:2128` | `a * b` |
| `core::ops::arith::<usize as Rem<Self>>::rem` | 43 | 6 | `crates/zed-kernel/src/num.rs:1230` | `a mod b` |
| `core::ops::arith::<usize as Sub<Self>>::sub` | 563 | 55 | `crates/zed-kernel/src/bits.rs:182` | `a - b` |
| `core::ops::arith::<usize as SubAssign<Self>>::sub_assign` | 102 | 14 | `crates/zed-kernel/src/eval.rs:765` | `a - b` |
| `core::ops::arith::Add::add` | 18 | 2 | `crates/zedc/src/canon/mod.rs:113` | `a + b` |
| `core::ops::arith::AddAssign::add_assign` | 21 | 2 | `crates/zed-kernel/src/print.rs:776` | `a + b` |
| `core::ops::arith::Div::div` | 3 | 1 | `crates/zed-kernel/src/types/bdd/list.rs:135` | `a div b` |
| `core::ops::arith::Mul::mul` | 3 | 1 | `crates/zedc/src/store/negsssp.rs:695` | `a * b` |
| `core::ops::arith::Neg::neg` | 1 | 1 | `crates/zedc/src/axioms.rs:137` | `-a` |
| `core::ops::arith::Sub::sub` | 9 | 3 | `crates/zed-kernel/src/num.rs:915` | `a - b` |
| `core::ops::bit::<&bool as Not>::not` | 10 | 7 | `crates/zed-kernel/src/eval.rs:2251` | `!a` |
| `core::ops::bit::<&i128 as BitAnd<i128>>::bitand` | 3 | 1 | `crates/zedc/src/store/int.rs:139` | `bitAnd(a mod 2 ** 128, b)` |
| `core::ops::bit::<&i64 as BitAnd<i64>>::bitand` | 3 | 1 | `crates/zedc/src/store/int.rs:1836` | `bitAnd(a mod 2 ** 64, b)` |
| `core::ops::bit::<&u64 as Shr<usize>>::shr` | 3 | 1 | `crates/zedc/src/zir/legalize.rs:72` | `shr(a, n)` |
| `core::ops::bit::<bool as BitAndAssign<Self>>::bitand_assign` | 84 | 10 | `crates/zed-kernel/src/exact.rs:111` | `a && b` |
| `core::ops::bit::<bool as BitOr<Self>>::bitor` | 3 | 1 | `crates/zedc/src/store/presburger/deep.rs:617` | `a \|\| b` |
| `core::ops::bit::<bool as BitOrAssign<Self>>::bitor_assign` | 81 | 11 | `crates/zed-kernel/src/types/empty.rs:2457` | `a \|\| b` |
| `core::ops::bit::<bool as Not>::not` | 1117 | 85 | `crates/zed-kernel/src/bits.rs:118` | `!a` |
| `core::ops::bit::<i128 as BitXor<Self>>::bitxor` | 3 | 1 | `crates/zedc/src/store/preimage.rs:4892` | `bitXor(a mod 2 ** 128, b mod 2 ** 128)` |
| `core::ops::bit::<i128 as Shl<i64>>::shl` | 6 | 1 | `crates/zed-kernel/src/bits.rs:202` | `shl(a, n)` |
| `core::ops::bit::<i128 as Shl<u32>>::shl` | 3 | 1 | `crates/zedc/src/check/widen.rs:550` | `shl(a, n)` |
| `core::ops::bit::<i128 as Shr<i32>>::shr` | 6 | 1 | `crates/zedc/src/store/preimage.rs:4892` | `shr(a, n)` |
| `core::ops::bit::<i64 as BitAnd<Self>>::bitand` | 3 | 1 | `crates/zed-kernel/src/bits.rs:194` | `bitAnd(a, b)` |
| `core::ops::bit::<i64 as BitOr<Self>>::bitor` | 3 | 1 | `crates/zed-kernel/src/bits.rs:195` | `bitOr(a, b)` |
| `core::ops::bit::<i64 as BitXor<Self>>::bitxor` | 3 | 1 | `crates/zed-kernel/src/bits.rs:196` | `bitXor(a, b)` |
| `core::ops::bit::<i64 as Shr<Self>>::shr` | 3 | 1 | `crates/zed-kernel/src/bits.rs:210` | `shr(a, n)` |
| `core::ops::bit::<u128 as BitAnd<Self>>::bitand` | 3 | 1 | `crates/zed-kernel/src/num.rs:922` | `bitAnd(a, b)` |
| `core::ops::bit::<u128 as BitOr<Self>>::bitor` | 6 | 1 | `crates/zed-kernel/src/num.rs:1191` | `bitOr(a, b)` |
| `core::ops::bit::<u128 as Shl<i32>>::shl` | 6 | 1 | `crates/zed-kernel/src/num.rs:1191` | `shl(a, n)` |
| `core::ops::bit::<u128 as Shl<u32>>::shl` | 3 | 1 | `crates/zed-kernel/src/exact.rs:14` | `shl(a, n)` |
| `core::ops::bit::<u128 as Shr<i32>>::shr` | 12 | 2 | `crates/zed-kernel/src/exact.rs:16` | `shr(a, n)` |
| `core::ops::bit::<u32 as BitAnd<Self>>::bitand` | 42 | 3 | `crates/zed-kernel/src/num.rs:906` | `bitAnd(a, b)` |
| `core::ops::bit::<u32 as BitOr<Self>>::bitor` | 9 | 2 | `crates/zed-kernel/src/num.rs:906` | `bitOr(a, b)` |
| `core::ops::bit::<u32 as BitXor<Self>>::bitxor` | 6 | 1 | `crates/zedc/src/stage.rs:498` | `bitXor(a, b)` |
| `core::ops::bit::<u32 as Not>::not` | 1 | 1 | `crates/zedc/src/stage.rs:421` | `bitNot(a, width: 32)` |
| `core::ops::bit::<u32 as Shl<Self>>::shl` | 6 | 1 | `crates/zedc/src/stage.rs:498` | `shl(a, n)` |
| `core::ops::bit::<u32 as Shl<i32>>::shl` | 9 | 1 | `crates/zed-kernel/src/num.rs:906` | `shl(a, n)` |
| `core::ops::bit::<u32 as Shr<Self>>::shr` | 3 | 1 | `crates/zedc/src/store/int.rs:1995` | `shr(a, n)` |
| `core::ops::bit::<u32 as Shr<i32>>::shr` | 3 | 1 | `crates/zed-kernel/src/num.rs:903` | `shr(a, n)` |
| `core::ops::bit::<u64 as BitAnd<Self>>::bitand` | 48 | 8 | `crates/zed-kernel/src/address.rs:17` | `bitAnd(a, b)` |
| `core::ops::bit::<u64 as BitOr<Self>>::bitor` | 21 | 4 | `crates/zed-kernel/src/bits.rs:221` | `bitOr(a, b)` |
| `core::ops::bit::<u64 as BitOrAssign<Self>>::bitor_assign` | 6 | 2 | `crates/zed-kernel/src/exact.rs:71` | `bitOr(a, b)` |
| `core::ops::bit::<u64 as BitXor<Self>>::bitxor` | 45 | 4 | `crates/zed-kernel/src/eval.rs:1982` | `bitXor(a, b)` |
| `core::ops::bit::<u64 as Shl<Self>>::shl` | 3 | 1 | `crates/zed-kernel/src/num/bound.rs:373` | `shl(a, n)` |
| `core::ops::bit::<u64 as Shl<i32>>::shl` | 39 | 4 | `crates/zed-kernel/src/exact.rs:79` | `shl(a, n)` |
| `core::ops::bit::<u64 as Shl<u32>>::shl` | 12 | 3 | `crates/zed-kernel/src/bits.rs:218` | `shl(a, n)` |
| `core::ops::bit::<u64 as Shl<usize>>::shl` | 15 | 3 | `crates/zed-kernel/src/num.rs:1053` | `shl(a, n)` |
| `core::ops::bit::<u64 as Shr<i32>>::shr` | 45 | 6 | `crates/zed-kernel/src/eval.rs:1982` | `shr(a, n)` |
| `core::ops::bit::<u64 as Shr<u32>>::shr` | 15 | 4 | `crates/zed-kernel/src/bits.rs:220` | `shr(a, n)` |
| `core::ops::bit::<u64 as ShrAssign<i32>>::shr_assign` | 15 | 5 | `crates/zed-kernel/src/exact.rs:80` | `shr(a, n)` |
| `core::ops::bit::<u64 as ShrAssign<u32>>::shr_assign` | 3 | 1 | `crates/zedc/src/store/float.rs:56` | `shr(a, n)` |
| `core::ops::bit::<u8 as BitAnd<Self>>::bitand` | 132 | 6 | `crates/zed-kernel/src/types.rs:953` | `bitAnd(a, b)` |
| `core::ops::bit::<u8 as BitAndAssign<Self>>::bitand_assign` | 3 | 1 | `crates/zedc/src/check/ty.rs:2680` | `bitAnd(a, b)` |
| `core::ops::bit::<u8 as BitOr<Self>>::bitor` | 30 | 5 | `crates/zed-kernel/src/types.rs:976` | `bitOr(a, b)` |
| `core::ops::bit::<u8 as BitOrAssign<&u8>>::bitor_assign` | 3 | 1 | `crates/zedc/src/check/mod.rs:410` | `bitOr(a, b)` |
| `core::ops::bit::<u8 as BitOrAssign<Self>>::bitor_assign` | 21 | 2 | `crates/zedc/src/check/mod.rs:3985` | `bitOr(a, b)` |
| `core::ops::bit::<u8 as Not>::not` | 5 | 4 | `crates/zed-kernel/src/types.rs:1007` | `bitNot(a, width: 8)` |
| `core::ops::bit::<u8 as Shl<Self>>::shl` | 18 | 3 | `crates/zed-kernel/src/types.rs:619` | `shl(a, n)` |
| `core::ops::bit::<u8 as Shl<i32>>::shl` | 3 | 1 | `crates/zedc/src/address.rs:26` | `shl(a, n)` |
| `core::ops::bit::<u8 as Shl<usize>>::shl` | 3 | 1 | `crates/zedc/src/check/ty.rs:976` | `shl(a, n)` |
| `core::ops::bit::<u8 as Shr<&u8>>::shr` | 3 | 1 | `crates/zed-kernel/src/types/empty.rs:2823` | `shr(a, n)` |
| `core::ops::bit::<usize as BitAnd<Self>>::bitand` | 9 | 2 | `crates/zedc/src/parse/engine.rs:696` | `bitAnd(a, b)` |
| `core::ops::bit::<usize as BitOr<Self>>::bitor` | 3 | 1 | `crates/zedc/src/parse/engine.rs:490` | `bitOr(a, b)` |
| `core::ops::bit::<usize as BitXor<Self>>::bitxor` | 12 | 2 | `crates/zedc/src/store/presburger/deep/canon.rs:333` | `bitXor(a, b)` |
| `core::ops::bit::<usize as Not>::not` | 1 | 1 | `crates/zedc/src/parse/engine.rs:699` | `bitNot(a, width: 64)` |
| `core::ops::bit::<usize as Shl<Self>>::shl` | 6 | 2 | `crates/zed-kernel/src/num.rs:1028` | `shl(a, n)` |
| `core::ops::bit::<usize as Shl<u32>>::shl` | 3 | 1 | `crates/zed-kernel/src/exact.rs:195` | `shl(a, n)` |
| `core::ops::bit::<usize as Shr<Self>>::shr` | 3 | 1 | `crates/zedc/src/store/presburger/deep/canon.rs:334` | `shr(a, n)` |
| `core::ops::bit::Shl::shl` | 18 | 5 | `crates/zed-kernel/src/eval.rs:41` | `shl(a, n)` |
| `core::ops::deref::<&T as Deref>::deref` | 1269 | 85 | `crates/zed-kernel/src/bits.rs:166` | `x` |
| `core::ops::deref::<&mut T as Deref>::deref` | 345 | 52 | `crates/zed-kernel/src/bits.rs:166` | `x` |
| `core::ops::deref::Deref::deref` | 1 | 1 | `crates/zed-native/src/exe.rs:131` | `x` |
| `core::ops::index::Index::index` | 1710 | 75 | `crates/zed-kernel/src/bits.rs:129` | `xs[i]` |
| `core::ops::index::IndexMut::index_mut` | 100 | 25 | `crates/zed-kernel/src/address.rs:24` | row L6.13 |
| `core::ops::range::<Range<Idx> as Clone>::clone` | 3 | 2 | `crates/zed-kernel/src/types/empty.rs:1846` | `x` |
| `core::ops::range::Range<Idx>::contains` | 2 | 2 | `crates/zed-kernel/src/num.rs:1562` | `k in m` |
| `core::ops::range::RangeInclusive<Idx>::contains` | 1 | 1 | `crates/zedc/src/parse/grammar.rs:122` | `k in m` |
| `core::ops::try_trait::Try::branch` | 4 | 1 | `crates/zedc/src/store/presburger.rs:4533` | missing |
| `core::option::<Option<T> as Clone>::clone` | 54 | 15 | `crates/zed-kernel/src/eval.rs:841` | `x` |
| `core::option::<Option<T> as IntoIterator>::into_iter` | 20 | 12 | `crates/zed-kernel/src/types/bdd.rs:1319` | row STD-seq |
| `core::option::<Option<T> as Ord>::cmp` | 2 | 2 | `crates/zed-kernel/src/value.rs:616` | missing |
| `core::option::<Option<T> as PartialEq<Self>>::eq` | 255 | 30 | `crates/zed-kernel/src/deep.rs:305` | `a == b` |
| `core::option::<Option<T> as Try>::branch` | 494 | 38 | `crates/zed-kernel/src/eval.rs:139` | missing |
| `core::option::Option<&T>::cloned` | 54 | 20 | `crates/zed-kernel/src/eval.rs:2254` | `x` |
| `core::option::Option<&T>::copied` | 53 | 28 | `crates/zed-kernel/src/eval.rs:413` | `x` |
| `core::option::Option<Option<T>>::flatten` | 17 | 11 | `crates/zed-kernel/src/eval.rs:413` | missing |
| `core::option::Option<Result<T, E>>::transpose` | 5 | 4 | `crates/zed-native/src/link.rs:238` | missing |
| `core::option::Option<T>::and_then` | 79 | 32 | `crates/zed-kernel/src/deep.rs:409` | missing |
| `core::option::Option<T>::as_deref` | 14 | 8 | `crates/zed-kernel/src/types/print.rs:558` | `x` |
| `core::option::Option<T>::as_deref_mut` | 2 | 2 | `crates/zedc/src/elab.rs:908` | `x` |
| `core::option::Option<T>::as_mut` | 14 | 7 | `crates/zed-kernel/src/eval.rs:345` | `x` |
| `core::option::Option<T>::as_ref` | 155 | 31 | `crates/zed-kernel/src/eval.rs:139` | `x` |
| `core::option::Option<T>::expect` | 468 | 66 | `crates/zed-kernel/src/bits.rs:123` | row S.1d |
| `core::option::Option<T>::filter` | 57 | 20 | `crates/zed-kernel/src/types.rs:1075` | missing |
| `core::option::Option<T>::get_or_insert` | 14 | 7 | `crates/zed-kernel/src/types/empty.rs:1084` | missing |
| `core::option::Option<T>::get_or_insert_with` | 13 | 10 | `crates/zed-kernel/src/types/empty.rs:1180` | missing |
| `core::option::Option<T>::is_none` | 107 | 36 | `crates/zed-kernel/src/deep.rs:295` | missing |
| `core::option::Option<T>::is_none_or` | 43 | 16 | `crates/zed-kernel/src/types/bdd.rs:1441` | missing |
| `core::option::Option<T>::is_some` | 136 | 31 | `crates/zed-kernel/src/deep.rs:198` | missing |
| `core::option::Option<T>::is_some_and` | 90 | 40 | `crates/zed-kernel/src/eval.rs:1194` | missing |
| `core::option::Option<T>::iter` | 7 | 5 | `crates/zedc/src/check/walk.rs:2045` | row STD-seq |
| `core::option::Option<T>::map` | 198 | 50 | `crates/zed-kernel/src/eval.rs:970` | missing |
| `core::option::Option<T>::map_or` | 65 | 32 | `crates/zed-kernel/src/num.rs:134` | missing |
| `core::option::Option<T>::map_or_else` | 16 | 8 | `crates/zed-kernel/src/types/empty.rs:397` | missing |
| `core::option::Option<T>::ok_or` | 10 | 3 | `crates/zedc/src/parse/grammar.rs:241` | missing |
| `core::option::Option<T>::ok_or_else` | 37 | 13 | `crates/zed-kernel/src/family.rs:158` | missing |
| `core::option::Option<T>::or` | 8 | 5 | `crates/zed-kernel/src/types/empty.rs:227` | missing |
| `core::option::Option<T>::or_else` | 6 | 5 | `crates/zed-kernel/src/types/bdd.rs:1596` | missing |
| `core::option::Option<T>::replace` | 5 | 5 | `crates/zed-kernel/src/types/empty.rs:1316` | missing |
| `core::option::Option<T>::take` | 74 | 27 | `crates/zed-kernel/src/deep.rs:70` | missing |
| `core::option::Option<T>::unwrap` | 5 | 3 | `crates/zedc/src/check/mod.rs:4271` | row S.1d |
| `core::option::Option<T>::unwrap_or` | 79 | 39 | `crates/zed-kernel/src/num.rs:119` | missing |
| `core::option::Option<T>::unwrap_or_default` | 24 | 16 | `crates/zed-kernel/src/eval.rs:133` | missing |
| `core::option::Option<T>::unwrap_or_else` | 45 | 20 | `crates/zed-kernel/src/eval.rs:1889` | missing |
| `core::option::Option<T>::zip` | 6 | 4 | `crates/zed-kernel/src/words.rs:273` | missing |
| `core::pin::Pin<&'a mut T>::get_mut` | 1 | 1 | `crates/zed-kernel/src/frames.rs:107` | row L6.13 |
| `core::pin::Pin<Ptr>::as_mut` | 1 | 1 | `crates/zed-kernel/src/frames.rs:82` | `x` |
| `core::ptr::const_ptr::*const T::add` | 1 | 1 | `crates/zed-native/src/exe.rs:131` | row S.4 |
| `core::ptr::const_ptr::*const T::cast` | 3 | 2 | `crates/zedc/src/check/ty.rs:165` | missing |
| `core::ptr::const_ptr::<*const T as PartialEq<Self>>::eq` | 3 | 1 | `crates/zedc/src/store/presburger/deep.rs:103` | `a == b` |
| `core::ptr::eq` | 4 | 4 | `crates/zed-kernel/src/types/rec/walk.rs:218` | `a == b` |
| `core::ptr::null_mut` | 1 | 1 | `crates/zed-native/src/lib.rs:405` | missing |
| `core::result::<Result<T, E> as Clone>::clone` | 4 | 2 | `crates/zedc/src/query.rs:194` | `x` |
| `core::result::<Result<T, E> as PartialEq<Self>>::eq` | 3 | 1 | `crates/zedc/src/check/mod.rs:6030` | `a == b` |
| `core::result::<Result<T, E> as Try>::branch` | 967 | 54 | `crates/zed-kernel/src/bits.rs:57` | missing |
| `core::result::Result<T, E>::and_then` | 5 | 5 | `crates/zed-kernel/src/eval.rs:2103` | missing |
| `core::result::Result<T, E>::as_deref` | 1 | 1 | `crates/zedc/src/unit.rs:211` | `x` |
| `core::result::Result<T, E>::as_ref` | 1 | 1 | `crates/zedc/src/store/presburger.rs:5987` | `x` |
| `core::result::Result<T, E>::err` | 4 | 2 | `crates/zed-kernel/src/types/print.rs:953` | missing |
| `core::result::Result<T, E>::expect` | 67 | 26 | `crates/zed-kernel/src/eval.rs:421` | row S.1d |
| `core::result::Result<T, E>::is_err` | 6 | 4 | `crates/zed-kernel/src/eval.rs:1387` | missing |
| `core::result::Result<T, E>::is_ok` | 14 | 8 | `crates/zed-kernel/src/eval.rs:387` | missing |
| `core::result::Result<T, E>::is_ok_and` | 2 | 2 | `crates/zed-kernel/src/bits.rs:154` | missing |
| `core::result::Result<T, E>::map` | 31 | 15 | `crates/zed-kernel/src/bits.rs:232` | missing |
| `core::result::Result<T, E>::map_err` | 128 | 27 | `crates/zed-kernel/src/bits.rs:71` | missing |
| `core::result::Result<T, E>::map_or` | 1 | 1 | `crates/zedc/src/zir/mod.rs:886` | missing |
| `core::result::Result<T, E>::map_or_else` | 4 | 4 | `crates/zed-kernel/src/types/print.rs:356` | missing |
| `core::result::Result<T, E>::ok` | 71 | 27 | `crates/zed-kernel/src/eval.rs:2070` | missing |
| `core::result::Result<T, E>::or_else` | 3 | 1 | `crates/zedc/src/zir/binary.rs:422` | missing |
| `core::result::Result<T, E>::unwrap_or` | 1 | 1 | `crates/zed-native/src/exe.rs:125` | missing |
| `core::result::Result<T, E>::unwrap_or_else` | 8 | 6 | `crates/zed-native/src/hooks.rs:115` | missing |
| `core::slice::[T]::as_chunks` | 2 | 1 | `crates/zedc/src/ast/types.rs:356` | missing |
| `core::slice::[T]::binary_search` | 15 | 6 | `crates/zed-kernel/src/eval.rs:1387` | row STD-seq |
| `core::slice::[T]::binary_search_by` | 2 | 2 | `crates/zedc/src/run.rs:769` | row STD-seq |
| `core::slice::[T]::binary_search_by_key` | 3 | 2 | `crates/zed-kernel/src/num.rs:357` | row STD-seq |
| `core::slice::[T]::chunks` | 3 | 2 | `crates/zed-native/src/codegen.rs:185` | row STD-seq |
| `core::slice::[T]::clone_from_slice` | 1 | 1 | `crates/zedc/src/canon/mod.rs:159` | missing |
| `core::slice::[T]::contains` | 29 | 15 | `crates/zed-kernel/src/types/bes.rs:117` | row STD-seq |
| `core::slice::[T]::copy_from_slice` | 1 | 1 | `crates/zed-kernel/src/text.rs:372` | missing |
| `core::slice::[T]::ends_with` | 1 | 1 | `crates/zed-native/src/link.rs:256` | row STD-text |
| `core::slice::[T]::fill` | 5 | 4 | `crates/zed-kernel/src/address.rs:24` | missing |
| `core::slice::[T]::first` | 42 | 24 | `crates/zed-kernel/src/eval.rs:1442` | `xs.first` |
| `core::slice::[T]::first_mut` | 1 | 1 | `crates/zedc/src/store/int.rs:631` | row L6.13 |
| `core::slice::[T]::get` | 134 | 43 | `crates/zed-kernel/src/deep.rs:475` | `xs[i]` |
| `core::slice::[T]::get_mut` | 6 | 4 | `crates/zed-kernel/src/provenance.rs:656` | row L6.13 |
| `core::slice::[T]::is_empty` | 70 | 28 | `crates/zed-kernel/src/deep.rs:469` | `xs.count == 0` |
| `core::slice::[T]::iter` | 1519 | 90 | `crates/zed-kernel/src/bits.rs:60` | row STD-seq |
| `core::slice::[T]::iter_mut` | 41 | 15 | `crates/zed-kernel/src/bits.rs:164` | row L6.13 |
| `core::slice::[T]::last` | 60 | 35 | `crates/zed-kernel/src/bits.rs:123` | `xs.last` |
| `core::slice::[T]::last_mut` | 96 | 41 | `crates/zed-kernel/src/eval.rs:1498` | row L6.13 |
| `core::slice::[T]::len` | 253 | 55 | `crates/zed-kernel/src/bits.rs:170` | `xs.count` |
| `core::slice::[T]::partition_point` | 16 | 8 | `crates/zedc/src/docs.rs:22` | row STD-seq |
| `core::slice::[T]::reverse` | 29 | 17 | `crates/zed-kernel/src/num.rs:1242` | row STD-seq |
| `core::slice::[T]::select_nth_unstable` | 1 | 1 | `crates/zedc/src/store/live3.rs:503` | missing |
| `core::slice::[T]::select_nth_unstable_by` | 1 | 1 | `crates/zedc/src/store/live3.rs:368` | missing |
| `core::slice::[T]::sort_unstable` | 37 | 19 | `crates/zed-kernel/src/num/factor.rs:24` | `xs.sort(asc x -> x)` |
| `core::slice::[T]::sort_unstable_by` | 5 | 4 | `crates/zedc/src/store/preimage.rs:721` | `xs.sort(by: f)` |
| `core::slice::[T]::sort_unstable_by_key` | 5 | 4 | `crates/zed-kernel/src/num.rs:649` | `xs.sort(asc f)` |
| `core::slice::[T]::split` | 1 | 1 | `crates/zedc/src/run.rs:654` | row STD-seq |
| `core::slice::[T]::split_at_checked` | 1 | 1 | `crates/zed-native/src/exe.rs:55` | missing |
| `core::slice::[T]::split_at_mut` | 4 | 3 | `crates/zed-kernel/src/types.rs:1932` | row L6.13 |
| `core::slice::[T]::split_first` | 30 | 7 | `crates/zed-kernel/src/eval.rs:916` | missing |
| `core::slice::[T]::split_first_chunk` | 1 | 1 | `crates/zed-native/src/exe.rs:53` | missing |
| `core::slice::[T]::split_last` | 16 | 7 | `crates/zed-kernel/src/family.rs:133` | missing |
| `core::slice::[T]::starts_with` | 3 | 2 | `crates/zed-native/src/link.rs:256` | row STD-text |
| `core::slice::[T]::strip_prefix` | 2 | 1 | `crates/zedc/src/run.rs:796` | row STD-text |
| `core::slice::[T]::strip_suffix` | 1 | 1 | `crates/zedc/src/run.rs:659` | row STD-text |
| `core::slice::[T]::swap` | 7 | 5 | `crates/zed-kernel/src/eval.rs:1990` | row L6.13 |
| `core::slice::[T]::windows` | 11 | 9 | `crates/zed-kernel/src/value.rs:366` | row STD-seq |
| `core::slice::cmp::<[T] as Ord>::cmp` | 2 | 2 | `crates/zed-kernel/src/text.rs:283` | missing |
| `core::slice::cmp::<[T] as PartialEq<[U]>>::eq` | 9 | 2 | `crates/zed-kernel/src/value.rs:133` | `a == b` |
| `core::slice::cmp::<[T] as PartialOrd<Self>>::le` | 3 | 1 | `crates/zedc/src/store/presburger.rs:4630` | `a <= b` |
| `core::slice::iter::<Iter<'a, T> as Iterator>::all` | 74 | 19 | `crates/zed-kernel/src/num.rs:185` | `xs.all(p)` |
| `core::slice::iter::<Iter<'a, T> as Iterator>::any` | 85 | 27 | `crates/zed-kernel/src/eval.rs:1450` | `xs.any(p)` |
| `core::slice::iter::<Iter<'a, T> as Iterator>::find` | 32 | 19 | `crates/zed-kernel/src/eval.rs:1892` | `xs.where(p).first` |
| `core::slice::iter::<Iter<'a, T> as Iterator>::find_map` | 8 | 4 | `crates/zedc/src/check/mod.rs:4497` | row STD-seq |
| `core::slice::iter::<Iter<'a, T> as Iterator>::fold` | 40 | 17 | `crates/zed-kernel/src/provenance.rs:398` | `xs.foldl(z, f)` |
| `core::slice::iter::<Iter<'a, T> as Iterator>::for_each` | 30 | 8 | `crates/zedc/src/canon/binders.rs:74` | missing |
| `core::slice::iter::<Iter<'a, T> as Iterator>::next` | 15 | 6 | `crates/zed-kernel/src/deep.rs:232` | row STD-seq |
| `core::slice::iter::<Iter<'a, T> as Iterator>::position` | 22 | 13 | `crates/zed-kernel/src/types/rec.rs:668` | row STD-seq |
| `core::slice::iter::<Iter<'a, T> as Iterator>::rposition` | 1 | 1 | `crates/zedc/src/resolve.rs:814` | row STD-seq |
| `core::slice::iter::<IterMut<'a, T> as Iterator>::find` | 2 | 1 | `crates/zedc/src/check/mod.rs:2013` | `xs.where(p).first` |
| `core::slice::iter::<IterMut<'a, T> as Iterator>::for_each` | 5 | 1 | `crates/zedc/src/zir/canon.rs:89` | missing |
| `core::slice::iter::Iter<'a, T>::as_slice` | 3 | 2 | `crates/zedc/src/store/presburger/deep.rs:473` | `x` |
| `core::slice::raw::from_raw_parts` | 1 | 1 | `crates/zed-native/src/exe.rs:133` | missing |
| `core::slice::raw::from_ref` | 18 | 10 | `crates/zed-kernel/src/eval.rs:1470` | `[x]` |
| `core::str::converts::from_utf8` | 9 | 6 | `crates/zed-kernel/src/text.rs:666` | `fromUtf8(b)` |
| `core::str::error::Utf8Error::error_len` | 1 | 1 | `crates/zedc/src/source.rs:113` | missing |
| `core::str::error::Utf8Error::valid_up_to` | 1 | 1 | `crates/zedc/src/source.rs:112` | missing |
| `core::str::iter::<Bytes<'_> as Iterator>::all` | 7 | 4 | `crates/zed-kernel/src/num.rs:120` | `xs.all(p)` |
| `core::str::iter::<CharIndices<'a> as Iterator>::next` | 3 | 1 | `crates/zedc/src/zir/text.rs:1236` | row STD-text |
| `core::str::iter::<Chars<'a> as Iterator>::count` | 3 | 3 | `crates/zed-kernel/src/text.rs:292` | `len(s)` |
| `core::str::iter::<Chars<'a> as Iterator>::next` | 17 | 10 | `crates/zed-kernel/src/words.rs:146` | row STD-text |
| `core::str::iter::<RSplit<'a, P> as Iterator>::next` | 2 | 1 | `crates/zedc/src/resolve.rs:915` | row STD-seq |
| `core::str::iter::<Split<'a, P> as Iterator>::next` | 2 | 2 | `crates/zedc/src/run.rs:803` | row STD-seq |
| `core::str::str::as_bytes` | 43 | 15 | `crates/zed-kernel/src/text.rs:271` | `utf8(s)` |
| `core::str::str::bytes` | 13 | 7 | `crates/zed-kernel/src/num.rs:120` | `utf8(s)` |
| `core::str::str::char_indices` | 8 | 7 | `crates/zedc/src/ast/neglit.rs:151` | row STD-text |
| `core::str::str::chars` | 29 | 18 | `crates/zed-kernel/src/num.rs:1560` | row STD-text |
| `core::str::str::contains` | 12 | 6 | `crates/zed-kernel/src/types/print.rs:458` | row STD-text |
| `core::str::str::ends_with` | 14 | 5 | `crates/zed-kernel/src/words.rs:58` | row STD-text |
| `core::str::str::find` | 14 | 9 | `crates/zed-kernel/src/num.rs:114` | missing |
| `core::str::str::is_empty` | 21 | 7 | `crates/zed-kernel/src/num.rs:121` | `len(s) == 0` |
| `core::str::str::len` | 71 | 27 | `crates/zed-kernel/src/num.rs:134` | `utf8(s).count` |
| `core::str::str::lines` | 3 | 3 | `crates/zedc/src/run.rs:92` | `lines(s)` |
| `core::str::str::match_indices` | 2 | 1 | `crates/zedc/src/lex/string.rs:50` | row STD-text |
| `core::str::str::matches` | 2 | 2 | `crates/zedc/src/format.rs:417` | missing |
| `core::str::str::parse` | 19 | 11 | `crates/zed-kernel/src/num.rs:1026` | missing |
| `core::str::str::rfind` | 1 | 1 | `crates/zedc/src/lex/string.rs:361` | row STD-text |
| `core::str::str::rsplit` | 2 | 1 | `crates/zedc/src/resolve.rs:915` | missing |
| `core::str::str::rsplit_once` | 1 | 1 | `crates/zedc/src/check/ty.rs:2435` | row STD-text |
| `core::str::str::split` | 9 | 6 | `crates/zedc/src/fence.rs:23` | `s.split(t)` |
| `core::str::str::split_at` | 4 | 2 | `crates/zed-kernel/src/num.rs:1028` | missing |
| `core::str::str::split_once` | 12 | 6 | `crates/zed-kernel/src/num.rs:119` | row STD-text |
| `core::str::str::starts_with` | 39 | 15 | `crates/zed-kernel/src/words.rs:391` | row STD-text |
| `core::str::str::strip_prefix` | 21 | 12 | `crates/zed-kernel/src/num.rs:973` | row STD-text |
| `core::str::str::strip_suffix` | 8 | 6 | `crates/zed-kernel/src/words.rs:384` | row STD-text |
| `core::str::str::trim` | 10 | 5 | `crates/zed-kernel/src/print.rs:111` | `trim(s)` |
| `core::str::str::trim_end` | 2 | 2 | `crates/zed-kernel/src/print.rs:799` | row STD-text |
| `core::str::str::trim_end_matches` | 2 | 1 | `crates/zedc/src/lex/mod.rs:279` | row STD-text |
| `core::str::str::trim_matches` | 2 | 1 | `crates/zedc/src/parse/grammar.rs:143` | row STD-text |
| `core::str::str::trim_start` | 2 | 2 | `crates/zedc/src/fence.rs:62` | row STD-text |
| `core::str::str::trim_start_matches` | 5 | 3 | `crates/zedc/src/lex/string.rs:386` | row STD-text |
| `core::str::traits::<str as Ord>::cmp` | 3 | 3 | `crates/zedc/src/run.rs:769` | missing |
| `core::str::traits::<str as PartialEq<Self>>::eq` | 6 | 1 | `crates/zedc/src/check/walk.rs:1904` | `a == b` |
| `core::sync::atomic::Atomic<u64>::fetch_add` | 7 | 5 | `crates/zed-kernel/src/family.rs:50` | missing |
| `core::sync::atomic::Atomic<u64>::new` | 5 | 5 | `crates/zed-kernel/src/family.rs:39` | missing |
| `core::task::wake::Context<'a>::from_waker` | 1 | 1 | `crates/zed-kernel/src/frames.rs:80` | missing |
| `core::task::wake::Waker::noop` | 1 | 1 | `crates/zed-kernel/src/frames.rs:80` | missing |
| `core::tuple::<(U, T) as Default>::default` | 1 | 1 | `crates/zed-kernel/src/eval.rs:1660` | missing |
| `core::tuple::<(U, T) as Ord>::cmp` | 4 | 4 | `crates/zedc/src/check/mod.rs:205` | missing |
| `core::tuple::<(U, T) as PartialEq<Self>>::eq` | 18 | 4 | `crates/zed-native/src/hooks.rs:357` | `a == b` |
| `core::tuple::<(U, T) as PartialEq<Self>>::ne` | 6 | 2 | `crates/zedc/src/store/preimage.rs:1771` | `a != b` |
| `core::tuple::<(U, T) as PartialOrd<Self>>::le` | 3 | 1 | `crates/zedc/src/store/interval.rs:227` | `a <= b` |
| `core::tuple::<(V, U, T) as Ord>::cmp` | 3 | 3 | `crates/zed-kernel/src/num.rs:1430` | missing |
| `core::tuple::<(V, U, T) as PartialEq<Self>>::eq` | 3 | 1 | `crates/zedc/src/elab.rs:317` | `a == b` |
| `core::tuple::<(V, U, T) as PartialOrd<Self>>::lt` | 3 | 1 | `crates/zedc/src/store/presburger.rs:3519` | `a < b` |
| `cranelift_codegen::ir::builder::InstBuilder::band` | 2 | 1 | `crates/zed-native/src/codegen.rs:559` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::bitcast` | 2 | 1 | `crates/zed-native/src/codegen.rs:570` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::bor` | 1 | 1 | `crates/zed-native/src/codegen.rs:675` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::brif` | 5 | 1 | `crates/zed-native/src/codegen.rs:297` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::bxor_imm_s` | 1 | 1 | `crates/zed-native/src/codegen.rs:616` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::call` | 4 | 2 | `crates/zed-native/src/codegen.rs:261` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::call_indirect` | 1 | 1 | `crates/zed-native/src/codegen.rs:734` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::fadd` | 1 | 1 | `crates/zed-native/src/codegen.rs:657` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::fcmp` | 2 | 1 | `crates/zed-native/src/codegen.rs:575` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::fdiv` | 1 | 1 | `crates/zed-native/src/codegen.rs:662` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::fmax` | 1 | 1 | `crates/zed-native/src/codegen.rs:661` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::fmin` | 1 | 1 | `crates/zed-native/src/codegen.rs:660` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::fmul` | 1 | 1 | `crates/zed-native/src/codegen.rs:659` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::fneg` | 1 | 1 | `crates/zed-native/src/codegen.rs:609` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::fsub` | 1 | 1 | `crates/zed-native/src/codegen.rs:658` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::func_addr` | 2 | 2 | `crates/zed-native/src/codegen.rs:207` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::iadd_imm_s` | 1 | 1 | `crates/zed-native/src/codegen.rs:729` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::icmp` | 1 | 1 | `crates/zed-native/src/codegen.rs:633` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::icmp_imm_s` | 10 | 1 | `crates/zed-native/src/codegen.rs:295` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::iconst` | 18 | 2 | `crates/zed-native/src/codegen.rs:190` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::ineg` | 1 | 1 | `crates/zed-native/src/codegen.rs:602` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::jump` | 5 | 1 | `crates/zed-native/src/codegen.rs:552` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::return_` | 3 | 2 | `crates/zed-native/src/codegen.rs:188` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::sadd_overflow` | 1 | 1 | `crates/zed-native/src/codegen.rs:638` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::select` | 1 | 1 | `crates/zed-native/src/codegen.rs:578` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::smul_overflow` | 1 | 1 | `crates/zed-native/src/codegen.rs:640` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::ssub_overflow` | 1 | 1 | `crates/zed-native/src/codegen.rs:639` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::stack_load` | 2 | 1 | `crates/zed-native/src/codegen.rs:333` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::stack_store` | 2 | 1 | `crates/zed-native/src/codegen.rs:324` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::symbol_value` | 1 | 1 | `crates/zed-native/src/exe.rs:96` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::uextend` | 1 | 1 | `crates/zed-native/src/codegen.rs:583` | row S.4 |
| `cranelift_codegen::ir::extfunc::AbiParam::new` | 6 | 2 | `crates/zed-native/src/codegen.rs:59` | row S.4 |
| `cranelift_codegen::ir::instructions::<BlockArg as From<Value>>::from` | 2 | 1 | `crates/zed-native/src/codegen.rs:53` | row S.4 |
| `cranelift_codegen::ir::memflags::MemFlagsData::new` | 2 | 1 | `crates/zed-native/src/codegen.rs:570` | row S.4 |
| `cranelift_codegen::ir::stackslot::StackSlotData::new` | 1 | 1 | `crates/zed-native/src/codegen.rs:323` | row S.4 |
| `cranelift_codegen::isa::IsaBuilder<T>::finish` | 1 | 1 | `crates/zed-native/src/lib.rs:91` | row S.4 |
| `cranelift_codegen::isa::TargetFrontendConfig::pointer_type` | 1 | 1 | `crates/zed-native/src/exe.rs:74` | row S.4 |
| `cranelift_codegen::isa::dyn TargetIsa + 'a::frontend_config` | 2 | 2 | `crates/zed-native/src/codegen.rs:195` | row S.4 |
| `cranelift_codegen::settings::<Builder as Configurable>::set` | 1 | 1 | `crates/zed-native/src/lib.rs:67` | row S.4 |
| `cranelift_codegen::settings::Flags::new` | 1 | 1 | `crates/zed-native/src/lib.rs:91` | row S.4 |
| `cranelift_codegen::settings::builder` | 1 | 1 | `crates/zed-native/src/lib.rs:66` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::append_block_param` | 1 | 1 | `crates/zed-native/src/codegen.rs:539` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::append_block_params_for_function_params` | 2 | 2 | `crates/zed-native/src/codegen.rs:176` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::block_params` | 4 | 2 | `crates/zed-native/src/codegen.rs:178` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::create_block` | 20 | 2 | `crates/zed-native/src/codegen.rs:175` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::create_sized_stack_slot` | 1 | 1 | `crates/zed-native/src/codegen.rs:323` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::finalize` | 2 | 2 | `crates/zed-native/src/codegen.rs:196` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::import_signature` | 1 | 1 | `crates/zed-native/src/codegen.rs:732` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::ins` | 76 | 2 | `crates/zed-native/src/codegen.rs:188` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::inst_results` | 5 | 2 | `crates/zed-native/src/codegen.rs:262` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::new` | 2 | 2 | `crates/zed-native/src/codegen.rs:174` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::seal_all_blocks` | 1 | 1 | `crates/zed-native/src/codegen.rs:194` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::seal_block` | 1 | 1 | `crates/zed-native/src/exe.rs:93` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::switch_to_block` | 20 | 2 | `crates/zed-native/src/codegen.rs:177` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilderContext::new` | 2 | 2 | `crates/zed-native/src/codegen.rs:172` | row S.4 |
| `cranelift_frontend::switch::Switch::emit` | 1 | 1 | `crates/zed-native/src/codegen.rs:761` | row S.4 |
| `cranelift_frontend::switch::Switch::new` | 1 | 1 | `crates/zed-native/src/codegen.rs:757` | row S.4 |
| `cranelift_frontend::switch::Switch::set_entry` | 1 | 1 | `crates/zed-native/src/codegen.rs:759` | row S.4 |
| `cranelift_jit::backend::JITBuilder::memory_provider` | 1 | 1 | `crates/zed-native/src/lib.rs:154` | row S.4 |
| `cranelift_jit::backend::JITBuilder::symbol` | 1 | 1 | `crates/zed-native/src/lib.rs:156` | row S.4 |
| `cranelift_jit::backend::JITBuilder::with_isa` | 1 | 1 | `crates/zed-native/src/lib.rs:153` | row S.4 |
| `cranelift_jit::backend::JITModule::finalize_definitions` | 1 | 1 | `crates/zed-native/src/lib.rs:160` | row S.4 |
| `cranelift_jit::backend::JITModule::free_memory` | 1 | 1 | `crates/zed-native/src/lib.rs:109` | row S.4 |
| `cranelift_jit::backend::JITModule::get_finalized_function` | 1 | 1 | `crates/zed-native/src/lib.rs:162` | row S.4 |
| `cranelift_jit::backend::JITModule::new` | 1 | 1 | `crates/zed-native/src/lib.rs:158` | row S.4 |
| `cranelift_jit::memory::system::SystemMemoryProvider::new` | 1 | 1 | `crates/zed-native/src/lib.rs:129` | row S.4 |
| `cranelift_module::data_context::DataDescription::define` | 1 | 1 | `crates/zed-native/src/exe.rs:72` | row S.4 |
| `cranelift_module::data_context::DataDescription::new` | 1 | 1 | `crates/zed-native/src/exe.rs:71` | row S.4 |
| `cranelift_module::default_libcall_names` | 4 | 1 | `crates/zed-native/src/lib.rs:23` | row S.4 |
| `cranelift_module::module::<&mut M as Module>::clear_context` | 2 | 2 | `crates/zed-native/src/codegen.rs:199` | row S.4 |
| `cranelift_module::module::<&mut M as Module>::declare_data_in_func` | 1 | 1 | `crates/zed-native/src/exe.rs:95` | row S.4 |
| `cranelift_module::module::<&mut M as Module>::isa` | 2 | 2 | `crates/zed-native/src/codegen.rs:195` | row S.4 |
| `cranelift_module::module::<&mut M as Module>::make_context` | 2 | 2 | `crates/zed-native/src/codegen.rs:170` | row S.4 |
| `cranelift_module::module::<&mut M as Module>::make_signature` | 1 | 1 | `crates/zed-native/src/exe.rs:75` | row S.4 |
| `cranelift_module::module::<&mut M as Module>::target_config` | 1 | 1 | `crates/zed-native/src/exe.rs:74` | row S.4 |
| `cranelift_module::module::Module::declare_data` | 1 | 1 | `crates/zed-native/src/exe.rs:69` | row S.4 |
| `cranelift_module::module::Module::declare_func_in_func` | 3 | 2 | `crates/zed-native/src/codegen.rs:277` | row S.4 |
| `cranelift_module::module::Module::declare_function` | 6 | 2 | `crates/zed-native/src/codegen.rs:125` | row S.4 |
| `cranelift_module::module::Module::define_data` | 1 | 1 | `crates/zed-native/src/exe.rs:73` | row S.4 |
| `cranelift_module::module::Module::define_function` | 2 | 2 | `crates/zed-native/src/codegen.rs:198` | row S.4 |
| `cranelift_module::module::Module::make_signature` | 1 | 1 | `crates/zed-native/src/codegen.rs:58` | row S.4 |
| `cranelift_native::builder` | 1 | 1 | `crates/zed-native/src/lib.rs:90` | row S.4 |
| `cranelift_object::backend::ObjectBuilder::new` | 1 | 1 | `crates/zed-native/src/lib.rs:234` | row S.4 |
| `cranelift_object::backend::ObjectModule::finish` | 2 | 1 | `crates/zed-native/src/lib.rs:208` | row S.4 |
| `cranelift_object::backend::ObjectModule::new` | 1 | 1 | `crates/zed-native/src/lib.rs:236` | row S.4 |
| `cranelift_object::backend::ObjectProduct::emit` | 2 | 1 | `crates/zed-native/src/lib.rs:208` | row S.4 |
| `imbl::hash::map::<GenericHashMap<K, V, S, P> as Clone>::clone` | 7 | 3 | `crates/zedc/src/store/preimage.rs:2530` | `x` |
| `imbl::hash::map::GenericHashMap<K, V, S, P>::get` | 5 | 3 | `crates/zedc/src/store/preimage.rs:1732` | `xs[i]` |
| `imbl::hash::map::GenericHashMap<K, V, S, P>::insert` | 3 | 3 | `crates/zedc/src/store/preimage.rs:2534` | row STD-seq |
| `imbl::hash::map::GenericHashMap<K, V, S, P>::new` | 8 | 3 | `crates/zedc/src/store/preimage.rs:1664` | `{}` |
| `imbl::hash::map::GenericHashMap<K, V, S, P>::update` | 4 | 2 | `crates/zedc/src/store/preimage.rs:1791` | row STD-seq |
| `imbl::hash::set::GenericHashSet<A, S, P>::contains` | 3 | 1 | `crates/zedc/src/store/presburger.rs:2481` | `k in m` |
| `imbl::hash::set::GenericHashSet<A, S, P>::insert` | 2 | 1 | `crates/zedc/src/store/presburger.rs:2495` | row STD-seq |
| `imbl::ord::map::<DiffIter<'a, 'b, K, V, P> as Iterator>::next` | 1 | 1 | `crates/zed-kernel/src/deep.rs:295` | row STD-seq |
| `imbl::ord::map::<GenericOrdMap<K, V, P> as Clone>::clone` | 21 | 6 | `crates/zed-kernel/src/family.rs:362` | `x` |
| `imbl::ord::map::<GenericOrdMap<K, V, P> as Extend<(RK, RV)>>::extend` | 1 | 1 | `crates/zed-kernel/src/family.rs:327` | row L6.13 |
| `imbl::ord::map::<GenericOrdMap<K, V, P> as Index<&Q>>::index` | 4 | 2 | `crates/zedc/src/store/conjuncts.rs:875` | `xs[i]` |
| `imbl::ord::map::<GenericOrdMap<K, V, P> as PartialEq<Self>>::eq` | 3 | 1 | `crates/zedc/src/store/product.rs:1637` | `a == b` |
| `imbl::ord::map::<Iter<'a, K, V, P> as Iterator>::next` | 5 | 3 | `crates/zed-kernel/src/deep.rs:240` | row STD-seq |
| `imbl::ord::map::<RangedIter<'a, K, V, P> as Iterator>::next` | 2 | 1 | `crates/zed-kernel/src/types/bdd.rs:1767` | row L5.8a |
| `imbl::ord::map::Entry<'a, K, V, P>::or_default` | 4 | 2 | `crates/zedc/src/store/conjuncts.rs:32` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::contains_key` | 19 | 7 | `crates/zed-kernel/src/provenance.rs:509` | `k in m` |
| `imbl::ord::map::GenericOrdMap<K, V, P>::diff` | 14 | 4 | `crates/zed-kernel/src/deep.rs:295` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::entry` | 4 | 2 | `crates/zedc/src/store/conjuncts.rs:32` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::get` | 79 | 11 | `crates/zed-kernel/src/eval.rs:139` | `xs[i]` |
| `imbl::ord::map::GenericOrdMap<K, V, P>::get_key_value` | 1 | 1 | `crates/zedc/src/store/product.rs:927` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::get_min` | 1 | 1 | `crates/zed-kernel/src/family.rs:404` | `xs.first` |
| `imbl::ord::map::GenericOrdMap<K, V, P>::get_mut` | 13 | 3 | `crates/zedc/src/store/conjuncts.rs:37` | missing |
| `imbl::ord::map::GenericOrdMap<K, V, P>::insert` | 57 | 10 | `crates/zed-kernel/src/eval.rs:134` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::is_empty` | 10 | 7 | `crates/zed-kernel/src/family.rs:71` | `xs.count == 0` |
| `imbl::ord::map::GenericOrdMap<K, V, P>::iter` | 23 | 10 | `crates/zed-kernel/src/deep.rs:173` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::keys` | 12 | 6 | `crates/zed-kernel/src/family.rs:312` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::len` | 31 | 7 | `crates/zed-kernel/src/family.rs:336` | `xs.count` |
| `imbl::ord::map::GenericOrdMap<K, V, P>::new` | 27 | 7 | `crates/zed-kernel/src/provenance.rs:327` | `{}` |
| `imbl::ord::map::GenericOrdMap<K, V, P>::ptr_eq` | 1 | 1 | `crates/zed-kernel/src/deep.rs:162` | missing |
| `imbl::ord::map::GenericOrdMap<K, V, P>::range` | 3 | 2 | `crates/zed-kernel/src/types/bdd.rs:1763` | row L5.8a |
| `imbl::ord::map::GenericOrdMap<K, V, P>::remove` | 42 | 6 | `crates/zed-kernel/src/provenance.rs:525` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::values` | 8 | 5 | `crates/zed-kernel/src/provenance.rs:422` | row STD-seq |
| `imbl::ord::set::<DiffIter<'a, 'b, A, P> as Iterator>::next` | 1 | 1 | `crates/zedc/src/check/ty.rs:710` | row STD-seq |
| `imbl::ord::set::<GenericOrdSet<A, P> as Clone>::clone` | 6 | 4 | `crates/zed-kernel/src/types/bdd.rs:1364` | `x` |
| `imbl::ord::set::<GenericOrdSet<A, P> as Extend<R>>::extend` | 1 | 1 | `crates/zedc/src/store/conjuncts.rs:533` | row L6.13 |
| `imbl::ord::set::<GenericOrdSet<A, P> as IntoIterator>::into_iter` | 1 | 1 | `crates/zedc/src/check/mod.rs:2453` | row STD-seq |
| `imbl::ord::set::<GenericOrdSet<A, P> as PartialEq<Self>>::eq` | 3 | 1 | `crates/zedc/src/store/conjuncts.rs:77` | `a == b` |
| `imbl::ord::set::<Iter<'a, A, P> as Iterator>::next` | 2 | 2 | `crates/zed-kernel/src/types/empty.rs:2181` | row STD-seq |
| `imbl::ord::set::GenericOrdSet<A, P>::contains` | 30 | 8 | `crates/zed-kernel/src/types.rs:1106` | `k in m` |
| `imbl::ord::set::GenericOrdSet<A, P>::diff` | 7 | 2 | `crates/zedc/src/check/ty.rs:707` | row STD-seq |
| `imbl::ord::set::GenericOrdSet<A, P>::insert` | 14 | 6 | `crates/zed-kernel/src/types.rs:1131` | row STD-seq |
| `imbl::ord::set::GenericOrdSet<A, P>::is_empty` | 15 | 6 | `crates/zed-kernel/src/types.rs:1035` | `xs.count == 0` |
| `imbl::ord::set::GenericOrdSet<A, P>::iter` | 35 | 9 | `crates/zed-kernel/src/types.rs:757` | row STD-seq |
| `imbl::ord::set::GenericOrdSet<A, P>::len` | 25 | 5 | `crates/zed-kernel/src/types.rs:1105` | `xs.count` |
| `imbl::ord::set::GenericOrdSet<A, P>::new` | 5 | 3 | `crates/zed-kernel/src/types/bdd.rs:1386` | `{}` |
| `imbl::ord::set::GenericOrdSet<A, P>::remove` | 7 | 3 | `crates/zed-kernel/src/types.rs:1137` | row STD-seq |
| `imbl::ord::set::GenericOrdSet<A, P>::unit` | 2 | 1 | `crates/zedc/src/store/conjuncts.rs:583` | row STD-seq |
| `imbl::vector::<GenericVector<A, P> as Clone>::clone` | 9 | 3 | `crates/zed-kernel/src/eval.rs:804` | `x` |
| `imbl::vector::<GenericVector<A, P> as Extend<A>>::extend` | 1 | 1 | `crates/zed-kernel/src/eval.rs:440` | row L6.13 |
| `imbl::vector::<GenericVector<A, P> as Index<usize>>::index` | 32 | 1 | `crates/zedc/src/resolve.rs:741` | `xs[i]` |
| `imbl::vector::GenericVector<A, P>::append` | 1 | 1 | `crates/zedc/src/resolve.rs:884` | row L6.13 |
| `imbl::vector::GenericVector<A, P>::front` | 1 | 1 | `crates/zedc/src/elab.rs:357` | `xs.first` |
| `imbl::vector::GenericVector<A, P>::iter` | 3 | 2 | `crates/zed-kernel/src/provenance.rs:201` | row STD-seq |
| `imbl::vector::GenericVector<A, P>::last` | 1 | 1 | `crates/zed-kernel/src/provenance.rs:184` | `xs.last` |
| `imbl::vector::GenericVector<A, P>::len` | 20 | 6 | `crates/zed-kernel/src/eval.rs:371` | `xs.count` |
| `imbl::vector::GenericVector<A, P>::new` | 2 | 2 | `crates/zedc/src/resolve.rs:708` | `[]` |
| `imbl::vector::GenericVector<A, P>::pop_back` | 1 | 1 | `crates/zed-kernel/src/eval.rs:770` | row STD-seq |
| `imbl::vector::GenericVector<A, P>::ptr_eq` | 1 | 1 | `crates/zedc/src/elab.rs:363` | missing |
| `imbl::vector::GenericVector<A, P>::push_back` | 5 | 2 | `crates/zed-kernel/src/eval.rs:729` | row L6.13 |
| `imbl::vector::GenericVector<A, P>::truncate` | 5 | 1 | `crates/zed-kernel/src/eval.rs:385` | missing |
| `imbl::vector::GenericVector<A, P>::unit` | 1 | 1 | `crates/zedc/src/store/product.rs:2880` | row STD-seq |
| `libc::mmap` | 1 | 1 | `crates/zed-native/src/lib.rs:404` | row S.4 |
| `libc::mprotect` | 1 | 1 | `crates/zed-native/src/lib.rs:424` | row S.4 |
| `libc::munmap` | 1 | 1 | `crates/zed-native/src/lib.rs:481` | row S.4 |
| `num_bigint::bigint::<&BigInt as Neg>::neg` | 10 | 3 | `crates/zed-kernel/src/num.rs:568` | `-a` |
| `num_bigint::bigint::<BigInt as Clone>::clone` | 32 | 2 | `crates/zed-kernel/src/num.rs:145` | `x` |
| `num_bigint::bigint::<BigInt as Integer>::div_ceil` | 2 | 1 | `crates/zedc/src/store/int.rs:548` | missing |
| `num_bigint::bigint::<BigInt as Integer>::div_floor` | 4 | 1 | `crates/zedc/src/store/int.rs:182` | `a div b` |
| `num_bigint::bigint::<BigInt as Integer>::div_rem` | 2 | 1 | `crates/zed-kernel/src/num.rs:1048` | missing |
| `num_bigint::bigint::<BigInt as Integer>::gcd` | 8 | 2 | `crates/zed-kernel/src/num.rs:962` | row STD-num |
| `num_bigint::bigint::<BigInt as Integer>::is_even` | 1 | 1 | `crates/zed-kernel/src/num.rs:225` | `a mod 2 == 0` |
| `num_bigint::bigint::<BigInt as Integer>::is_multiple_of` | 1 | 1 | `crates/zedc/src/store/int.rs:542` | `a mod b == 0` |
| `num_bigint::bigint::<BigInt as Integer>::is_odd` | 2 | 1 | `crates/zedc/src/store/int.rs:140` | `a mod 2 == 1` |
| `num_bigint::bigint::<BigInt as Integer>::mod_floor` | 5 | 1 | `crates/zedc/src/store/int.rs:193` | `a mod b` |
| `num_bigint::bigint::<BigInt as Neg>::neg` | 9 | 5 | `crates/zed-kernel/src/eval.rs:2192` | `-a` |
| `num_bigint::bigint::<BigInt as One>::is_one` | 11 | 2 | `crates/zed-kernel/src/num.rs:57` | `a == 1` |
| `num_bigint::bigint::<BigInt as One>::one` | 8 | 2 | `crates/zed-kernel/src/bits.rs:252` | `1` |
| `num_bigint::bigint::<BigInt as Ord>::cmp` | 3 | 3 | `crates/zed-kernel/src/num.rs:1374` | missing |
| `num_bigint::bigint::<BigInt as PartialEq<Self>>::eq` | 24 | 2 | `crates/zed-kernel/src/num.rs:1442` | `a == b` |
| `num_bigint::bigint::<BigInt as Signed>::abs` | 1 | 1 | `crates/zed-kernel/src/num.rs:356` | `abs(a)` |
| `num_bigint::bigint::<BigInt as Signed>::is_negative` | 4 | 1 | `crates/zed-kernel/src/num.rs:174` | `a < 0` |
| `num_bigint::bigint::<BigInt as Signed>::is_positive` | 3 | 1 | `crates/zed-kernel/src/num.rs:229` | `a > 0` |
| `num_bigint::bigint::<BigInt as Zero>::is_zero` | 21 | 2 | `crates/zed-kernel/src/num.rs:46` | `a == 0` |
| `num_bigint::bigint::<BigInt as Zero>::zero` | 7 | 2 | `crates/zed-kernel/src/num.rs:673` | `0` |
| `num_bigint::bigint::<Sign as Ord>::cmp` | 2 | 2 | `crates/zed-kernel/src/num.rs:1376` | missing |
| `num_bigint::bigint::<Sign as PartialEq<Self>>::eq` | 45 | 4 | `crates/zed-kernel/src/num.rs:279` | `a == b` |
| `num_bigint::bigint::BigInt::bits` | 37 | 2 | `crates/zed-kernel/src/num.rs:236` | row STD-num |
| `num_bigint::bigint::BigInt::from_biguint` | 8 | 5 | `crates/zed-kernel/src/num.rs:137` | `n * a` |
| `num_bigint::bigint::BigInt::into_parts` | 4 | 2 | `crates/zed-kernel/src/num.rs:696` | missing |
| `num_bigint::bigint::BigInt::magnitude` | 60 | 4 | `crates/zed-kernel/src/bits.rs:145` | `abs(a)` |
| `num_bigint::bigint::BigInt::nth_root` | 1 | 1 | `crates/zedc/src/store/int.rs:2094` | row STD-num |
| `num_bigint::bigint::BigInt::pow` | 1 | 1 | `crates/zedc/src/store/int.rs:2095` | `a ** n` |
| `num_bigint::bigint::BigInt::sign` | 21 | 3 | `crates/zed-kernel/src/num.rs:279` | missing |
| `num_bigint::bigint::BigInt::to_biguint` | 1 | 1 | `crates/zed-kernel/src/num.rs:392` | missing |
| `num_bigint::bigint::BigInt::trailing_zeros` | 8 | 2 | `crates/zed-kernel/src/num.rs:1040` | missing |
| `num_bigint::bigint::addition::<&BigInt as Add<BigInt>>::add` | 9 | 1 | `crates/zedc/src/store/int.rs:527` | `a + b` |
| `num_bigint::bigint::addition::<&BigInt as Add<Self>>::add` | 27 | 3 | `crates/zed-kernel/src/num.rs:428` | `a + b` |
| `num_bigint::bigint::addition::<&BigInt as Add<u32>>::add` | 9 | 1 | `crates/zedc/src/store/int.rs:454` | `a + b` |
| `num_bigint::bigint::addition::<&BigInt as Add<u64>>::add` | 21 | 2 | `crates/zed-kernel/src/num/bound.rs:96` | `a + b` |
| `num_bigint::bigint::addition::<BigInt as Add<&BigInt>>::add` | 9 | 1 | `crates/zedc/src/store/int.rs:522` | `a + b` |
| `num_bigint::bigint::addition::<BigInt as Add<Self>>::add` | 12 | 2 | `crates/zed-kernel/src/num.rs:419` | `a + b` |
| `num_bigint::bigint::addition::<BigInt as Add<u32>>::add` | 3 | 1 | `crates/zedc/src/store/int.rs:2096` | `a + b` |
| `num_bigint::bigint::addition::<BigInt as AddAssign<Self>>::add_assign` | 15 | 3 | `crates/zed-kernel/src/num.rs:238` | `a + b` |
| `num_bigint::bigint::addition::<BigInt as AddAssign<u32>>::add_assign` | 3 | 1 | `crates/zedc/src/store/int.rs:480` | `a + b` |
| `num_bigint::bigint::addition::<BigInt as AddAssign<u64>>::add_assign` | 9 | 3 | `crates/zed-kernel/src/num.rs:93` | `a + b` |
| `num_bigint::bigint::convert::<BigInt as From<BigUint>>::from` | 33 | 5 | `crates/zed-kernel/src/bits.rs:236` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<i128>>::from` | 2 | 1 | `crates/zedc/src/store/int.rs:102` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<i32>>::from` | 6 | 3 | `crates/zed-kernel/src/bits.rs:145` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<i64>>::from` | 10 | 5 | `crates/zed-kernel/src/eval.rs:2192` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<u128>>::from` | 1 | 1 | `crates/zedc/src/store/int.rs:168` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<u32>>::from` | 7 | 1 | `crates/zedc/src/store/int.rs:558` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<u64>>::from` | 14 | 4 | `crates/zed-kernel/src/bits.rs:50` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<usize>>::from` | 1 | 1 | `crates/zed-kernel/src/words.rs:119` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as ToPrimitive>::to_i64` | 3 | 2 | `crates/zed-kernel/src/num/bound.rs:104` | missing |
| `num_bigint::bigint::convert::<BigInt as ToPrimitive>::to_u64` | 2 | 1 | `crates/zed-kernel/src/num/bound.rs:117` | missing |
| `num_bigint::bigint::convert::<i128 as TryFrom<&BigInt>>::try_from` | 3 | 1 | `crates/zedc/src/store/int.rs:87` | missing |
| `num_bigint::bigint::convert::<i64 as TryFrom<&BigInt>>::try_from` | 2 | 1 | `crates/zedc/src/store/int.rs:1632` | missing |
| `num_bigint::bigint::convert::<u64 as TryFrom<&BigInt>>::try_from` | 5 | 1 | `crates/zedc/src/store/int.rs:394` | missing |
| `num_bigint::bigint::division::<&BigInt as Rem<Self>>::rem` | 6 | 1 | `crates/zed-kernel/src/num.rs:962` | `if a < 0 { -((-a) mod abs(b)) } else { a mod abs(b) }` |
| `num_bigint::bigint::division::<BigInt as Div<&BigInt>>::div` | 9 | 2 | `crates/zed-kernel/src/num.rs:953` | `if (a < 0) != (b < 0) { -(abs(a) div abs(b)) } else { abs(a) div abs(b) }` |
| `num_bigint::bigint::division::<BigInt as Div<Self>>::div` | 18 | 2 | `crates/zed-kernel/src/num.rs:953` | `if (a < 0) != (b < 0) { -(abs(a) div abs(b)) } else { abs(a) div abs(b) }` |
| `num_bigint::bigint::division::<BigInt as Euclid>::div_euclid` | 1 | 1 | `crates/zed-kernel/src/num.rs:743` | `a div b` |
| `num_bigint::bigint::multiplication::<&BigInt as Mul<BigInt>>::mul` | 15 | 2 | `crates/zed-kernel/src/num.rs:494` | `a * b` |
| `num_bigint::bigint::multiplication::<&BigInt as Mul<Self>>::mul` | 81 | 2 | `crates/zed-kernel/src/num.rs:446` | `a * b` |
| `num_bigint::bigint::multiplication::<&BigInt as Mul<u32>>::mul` | 3 | 1 | `crates/zed-kernel/src/num.rs:238` | `a * b` |
| `num_bigint::bigint::multiplication::<&BigInt as Mul<u64>>::mul` | 3 | 1 | `crates/zed-kernel/src/num.rs:634` | `a * b` |
| `num_bigint::bigint::multiplication::<BigInt as Mul<&BigInt>>::mul` | 6 | 1 | `crates/zed-kernel/src/num.rs:497` | `a * b` |
| `num_bigint::bigint::multiplication::<BigInt as Mul<Self>>::mul` | 12 | 1 | `crates/zed-kernel/src/num.rs:162` | `a * b` |
| `num_bigint::bigint::multiplication::<BigInt as MulAssign<Self>>::mul_assign` | 3 | 1 | `crates/zed-kernel/src/num.rs:217` | `a * b` |
| `num_bigint::bigint::multiplication::<i32 as Mul<BigInt>>::mul` | 6 | 1 | `crates/zed-kernel/src/num.rs:953` | `a * b` |
| `num_bigint::bigint::power::<BigInt as Pow<&BigUint>>::pow` | 1 | 1 | `crates/zed-kernel/src/num.rs:217` | `a ** n` |
| `num_bigint::bigint::power::<BigInt as Pow<u32>>::pow` | 2 | 1 | `crates/zed-kernel/src/num.rs:1534` | `a ** n` |
| `num_bigint::bigint::shift::<&BigInt as Shl<u32>>::shl` | 3 | 1 | `crates/zedc/src/store/int.rs:1102` | `shl(a, n)` |
| `num_bigint::bigint::shift::<&BigInt as Shl<u64>>::shl` | 6 | 1 | `crates/zedc/src/store/int.rs:522` | `shl(a, n)` |
| `num_bigint::bigint::shift::<&BigInt as Shr<u64>>::shr` | 15 | 1 | `crates/zedc/src/store/int.rs:416` | `shr(a, n)` |
| `num_bigint::bigint::shift::<BigInt as Shl<u32>>::shl` | 6 | 1 | `crates/zedc/src/store/int.rs:1760` | `shl(a, n)` |
| `num_bigint::bigint::shift::<BigInt as Shl<u64>>::shl` | 12 | 2 | `crates/zed-kernel/src/num.rs:162` | `shl(a, n)` |
| `num_bigint::bigint::shift::<BigInt as Shr<u32>>::shr` | 6 | 1 | `crates/zedc/src/store/int.rs:1231` | `shr(a, n)` |
| `num_bigint::bigint::shift::<BigInt as Shr<u64>>::shr` | 3 | 1 | `crates/zed-kernel/src/num.rs:1041` | `shr(a, n)` |
| `num_bigint::bigint::shift::<BigInt as ShrAssign<u64>>::shr_assign` | 6 | 1 | `crates/zedc/src/store/int.rs:477` | `shr(a, n)` |
| `num_bigint::bigint::subtraction::<&BigInt as Sub<BigInt>>::sub` | 3 | 1 | `crates/zedc/src/store/int.rs:1343` | `a - b` |
| `num_bigint::bigint::subtraction::<&BigInt as Sub<Self>>::sub` | 42 | 3 | `crates/zed-kernel/src/num.rs:389` | `a - b` |
| `num_bigint::bigint::subtraction::<&BigInt as Sub<i32>>::sub` | 3 | 1 | `crates/zed-kernel/src/num/bound.rs:249` | `a - b` |
| `num_bigint::bigint::subtraction::<&BigInt as Sub<u64>>::sub` | 3 | 1 | `crates/zedc/src/store/int.rs:1215` | `a - b` |
| `num_bigint::bigint::subtraction::<BigInt as Sub<&BigInt>>::sub` | 9 | 2 | `crates/zed-kernel/src/num.rs:486` | `a - b` |
| `num_bigint::bigint::subtraction::<BigInt as Sub<Self>>::sub` | 9 | 2 | `crates/zed-kernel/src/num.rs:363` | `a - b` |
| `num_bigint::bigint::subtraction::<BigInt as Sub<i32>>::sub` | 3 | 1 | `crates/zed-kernel/src/num.rs:236` | `a - b` |
| `num_bigint::bigint::subtraction::<BigInt as Sub<u64>>::sub` | 9 | 3 | `crates/zed-kernel/src/num.rs:144` | `a - b` |
| `num_bigint::bigint::subtraction::<BigInt as SubAssign<&BigInt>>::sub_assign` | 3 | 1 | `crates/zedc/src/store/int.rs:1103` | `a - b` |
| `num_bigint::bigint::subtraction::<BigInt as SubAssign<u64>>::sub_assign` | 3 | 1 | `crates/zed-kernel/src/num.rs:96` | `a - b` |
| `num_bigint::biguint::<BigUint as Clone>::clone` | 54 | 6 | `crates/zed-kernel/src/bits.rs:232` | `x` |
| `num_bigint::biguint::<BigUint as Integer>::div_rem` | 5 | 2 | `crates/zed-kernel/src/num/bound.rs:85` | `(a div b, a mod b)` |
| `num_bigint::biguint::<BigUint as Integer>::gcd` | 4 | 1 | `crates/zedc/src/store/int.rs:778` | row STD-num |
| `num_bigint::biguint::<BigUint as Integer>::is_multiple_of` | 2 | 1 | `crates/zedc/src/store/int.rs:1053` | `a mod b == 0` |
| `num_bigint::biguint::<BigUint as Integer>::lcm` | 1 | 1 | `crates/zedc/src/store/int.rs:2293` | row STD-num |
| `num_bigint::biguint::<BigUint as One>::is_one` | 20 | 3 | `crates/zed-kernel/src/num.rs:628` | `a == 1` |
| `num_bigint::biguint::<BigUint as One>::one` | 10 | 3 | `crates/zed-kernel/src/num.rs:1122` | `1` |
| `num_bigint::biguint::<BigUint as Ord>::cmp` | 7 | 3 | `crates/zed-kernel/src/num/bound.rs:107` | missing |
| `num_bigint::biguint::<BigUint as PartialEq<Self>>::eq` | 27 | 4 | `crates/zed-kernel/src/num/bound.rs:265` | `a == b` |
| `num_bigint::biguint::<BigUint as Zero>::is_zero` | 16 | 4 | `crates/zed-kernel/src/num.rs:599` | `a == 0` |
| `num_bigint::biguint::<BigUint as Zero>::zero` | 4 | 3 | `crates/zed-kernel/src/num.rs:1235` | `0` |
| `num_bigint::biguint::BigUint::bit` | 6 | 3 | `crates/zed-kernel/src/num.rs:651` | row STD-num |
| `num_bigint::biguint::BigUint::bits` | 35 | 4 | `crates/zed-kernel/src/bits.rs:244` | row STD-num |
| `num_bigint::biguint::BigUint::count_ones` | 1 | 1 | `crates/zed-kernel/src/bits.rs:242` | `popCount(a)` |
| `num_bigint::biguint::BigUint::from_bytes_le` | 1 | 1 | `crates/zedc/src/zir/binary.rs:554` | row STD-num |
| `num_bigint::biguint::BigUint::from_slice` | 1 | 1 | `crates/zed-kernel/src/num.rs:1243` | missing |
| `num_bigint::biguint::BigUint::iter_u64_digits` | 8 | 3 | `crates/zed-kernel/src/num.rs:1189` | missing |
| `num_bigint::biguint::BigUint::modpow` | 4 | 2 | `crates/zed-kernel/src/num.rs:713` | row STD-num |
| `num_bigint::biguint::BigUint::nth_root` | 1 | 1 | `crates/zedc/src/store/int.rs:870` | row STD-num |
| `num_bigint::biguint::BigUint::parse_bytes` | 1 | 1 | `crates/zed-kernel/src/value.rs:455` | row STD-num |
| `num_bigint::biguint::BigUint::pow` | 2 | 2 | `crates/zed-kernel/src/num.rs:1010` | `a ** n` |
| `num_bigint::biguint::BigUint::sqrt` | 1 | 1 | `crates/zedc/src/store/int.rs:602` | row STD-num |
| `num_bigint::biguint::BigUint::trailing_zeros` | 9 | 4 | `crates/zed-kernel/src/bits.rs:247` | missing |
| `num_bigint::biguint::addition::<&BigUint as Add<Self>>::add` | 9 | 1 | `crates/zedc/src/store/int.rs:1026` | `a + b` |
| `num_bigint::biguint::addition::<&BigUint as Add<u32>>::add` | 9 | 2 | `crates/zed-kernel/src/num.rs:1167` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as Add<&BigUint>>::add` | 6 | 2 | `crates/zed-kernel/src/types/empty.rs:741` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as Add<Self>>::add` | 24 | 3 | `crates/zed-kernel/src/num.rs:272` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as Add<u32>>::add` | 18 | 4 | `crates/zed-kernel/src/num.rs:284` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as Add<u64>>::add` | 6 | 2 | `crates/zed-kernel/src/num.rs:491` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as AddAssign<&BigUint>>::add_assign` | 3 | 1 | `crates/zedc/src/store/presburger/deep/canon.rs:538` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as AddAssign<Self>>::add_assign` | 18 | 5 | `crates/zed-kernel/src/num.rs:1143` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as AddAssign<u32>>::add_assign` | 6 | 1 | `crates/zed-kernel/src/num/bound.rs:50` | `a + b` |
| `num_bigint::biguint::bits::<&BigUint as BitAnd<Self>>::bitand` | 3 | 1 | `crates/zedc/src/store/int.rs:727` | `bitAnd(a, b)` |
| `num_bigint::biguint::bits::<BigUint as BitAnd<&BigUint>>::bitand` | 27 | 1 | `crates/zedc/src/store/int.rs:727` | `bitAnd(a, b)` |
| `num_bigint::biguint::bits::<BigUint as BitAnd<Self>>::bitand` | 9 | 2 | `crates/zed-kernel/src/bits.rs:237` | `bitAnd(a, b)` |
| `num_bigint::biguint::bits::<BigUint as BitOr<Self>>::bitor` | 3 | 1 | `crates/zed-kernel/src/bits.rs:238` | `bitOr(a, b)` |
| `num_bigint::biguint::bits::<BigUint as BitXor<Self>>::bitxor` | 3 | 1 | `crates/zed-kernel/src/bits.rs:239` | `bitXor(a, b)` |
| `num_bigint::biguint::convert::<BigUint as From<u128>>::from` | 1 | 1 | `crates/zed-kernel/src/num.rs:1218` | `int(a)` |
| `num_bigint::biguint::convert::<BigUint as From<u32>>::from` | 32 | 3 | `crates/zed-kernel/src/num.rs:161` | `int(a)` |
| `num_bigint::biguint::convert::<BigUint as From<u64>>::from` | 35 | 4 | `crates/zed-kernel/src/num.rs:425` | `int(a)` |
| `num_bigint::biguint::convert::<BigUint as From<usize>>::from` | 9 | 5 | `crates/zed-kernel/src/num.rs:135` | `int(a)` |
| `num_bigint::biguint::convert::<BigUint as ToPrimitive>::to_u128` | 1 | 1 | `crates/zed-kernel/src/words.rs:291` | missing |
| `num_bigint::biguint::convert::<BigUint as ToPrimitive>::to_u64` | 8 | 2 | `crates/zed-kernel/src/num.rs:330` | missing |
| `num_bigint::biguint::convert::<u128 as TryFrom<&BigUint>>::try_from` | 1 | 1 | `crates/zedc/src/store/int.rs:1944` | missing |
| `num_bigint::biguint::convert::<u32 as TryFrom<&BigUint>>::try_from` | 3 | 1 | `crates/zedc/src/store/int.rs:871` | missing |
| `num_bigint::biguint::convert::<u64 as TryFrom<&BigUint>>::try_from` | 3 | 1 | `crates/zedc/src/store/int.rs:1094` | missing |
| `num_bigint::biguint::convert::<u64 as TryFrom<BigUint>>::try_from` | 3 | 2 | `crates/zed-kernel/src/types/empty.rs:695` | missing |
| `num_bigint::biguint::division::<&BigUint as Div<Self>>::div` | 18 | 1 | `crates/zedc/src/store/int.rs:1053` | `a div b` |
| `num_bigint::biguint::division::<&BigUint as Rem<Self>>::rem` | 3 | 1 | `crates/zed-kernel/src/num.rs:1243` | `a mod b` |
| `num_bigint::biguint::division::<&BigUint as Rem<u32>>::rem` | 3 | 1 | `crates/zed-kernel/src/num.rs:1185` | `a mod b` |
| `num_bigint::biguint::division::<&BigUint as Rem<u64>>::rem` | 27 | 3 | `crates/zed-kernel/src/num.rs:329` | `a mod b` |
| `num_bigint::biguint::division::<BigUint as Div<&BigUint>>::div` | 6 | 1 | `crates/zedc/src/store/int.rs:1570` | `a div b` |
| `num_bigint::biguint::division::<BigUint as Rem<&BigUint>>::rem` | 9 | 2 | `crates/zed-kernel/src/num.rs:713` | `a mod b` |
| `num_bigint::biguint::division::<BigUint as RemAssign<Self>>::rem_assign` | 3 | 1 | `crates/zed-kernel/src/types/empty.rs:2040` | `a mod b` |
| `num_bigint::biguint::iter::<U64Digits<'_> as ExactSizeIterator>::len` | 3 | 3 | `crates/zed-kernel/src/num.rs:1227` | `xs.count` |
| `num_bigint::biguint::multiplication::<&BigUint as Mul<BigUint>>::mul` | 6 | 2 | `crates/zedc/src/store/int.rs:2033` | `a * b` |
| `num_bigint::biguint::multiplication::<&BigUint as Mul<Self>>::mul` | 45 | 3 | `crates/zed-kernel/src/num.rs:312` | `a * b` |
| `num_bigint::biguint::multiplication::<&BigUint as Mul<u32>>::mul` | 15 | 3 | `crates/zed-kernel/src/num.rs:284` | `a * b` |
| `num_bigint::biguint::multiplication::<&BigUint as Mul<u64>>::mul` | 9 | 2 | `crates/zed-kernel/src/types/empty.rs:699` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as Mul<&BigUint>>::mul` | 12 | 2 | `crates/zed-kernel/src/num.rs:621` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as Mul<Self>>::mul` | 16 | 2 | `crates/zed-kernel/src/num.rs:713` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as Mul<u32>>::mul` | 6 | 2 | `crates/zed-kernel/src/num.rs:1226` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as Mul<u64>>::mul` | 6 | 2 | `crates/zed-kernel/src/types/empty.rs:741` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as MulAssign<&BigUint>>::mul_assign` | 3 | 1 | `crates/zedc/src/store/int.rs:585` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as MulAssign<Self>>::mul_assign` | 6 | 2 | `crates/zed-kernel/src/num.rs:1128` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as MulAssign<u32>>::mul_assign` | 3 | 1 | `crates/zedc/src/store/int.rs:607` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as MulAssign<u64>>::mul_assign` | 9 | 2 | `crates/zed-kernel/src/types/empty.rs:700` | `a * b` |
| `num_bigint::biguint::power::<&BigUint as Pow<Self>>::pow` | 1 | 1 | `crates/zed-kernel/src/num.rs:646` | `a ** n` |
| `num_bigint::biguint::power::<BigUint as Pow<&BigUint>>::pow` | 2 | 2 | `crates/zed-kernel/src/num.rs:1128` | `a ** n` |
| `num_bigint::biguint::power::<BigUint as Pow<u32>>::pow` | 1 | 1 | `crates/zed-kernel/src/num.rs:1007` | `a ** n` |
| `num_bigint::biguint::power::<BigUint as Pow<u64>>::pow` | 1 | 1 | `crates/zed-kernel/src/num.rs:161` | `a ** n` |
| `num_bigint::biguint::shift::<&BigUint as Shl<u64>>::shl` | 15 | 2 | `crates/zed-kernel/src/num/bound.rs:85` | `shl(a, n)` |
| `num_bigint::biguint::shift::<&BigUint as Shl<usize>>::shl` | 6 | 1 | `crates/zed-kernel/src/num/bound.rs:119` | `shl(a, n)` |
| `num_bigint::biguint::shift::<&BigUint as Shr<u32>>::shr` | 3 | 1 | `crates/zed-kernel/src/num/bound.rs:366` | `shr(a, n)` |
| `num_bigint::biguint::shift::<&BigUint as Shr<u64>>::shr` | 12 | 2 | `crates/zed-kernel/src/num/bound.rs:48` | `shr(a, n)` |
| `num_bigint::biguint::shift::<BigUint as Shl<u32>>::shl` | 60 | 6 | `crates/zed-kernel/src/num.rs:135` | `shl(a, n)` |
| `num_bigint::biguint::shift::<BigUint as Shl<u64>>::shl` | 21 | 2 | `crates/zed-kernel/src/num.rs:163` | `shl(a, n)` |
| `num_bigint::biguint::shift::<BigUint as Shl<usize>>::shl` | 3 | 1 | `crates/zed-kernel/src/num.rs:1243` | `shl(a, n)` |
| `num_bigint::biguint::shift::<BigUint as ShlAssign<u64>>::shl_assign` | 3 | 1 | `crates/zed-kernel/src/num.rs:1132` | `shl(a, n)` |
| `num_bigint::biguint::shift::<BigUint as Shr<u32>>::shr` | 12 | 2 | `crates/zed-kernel/src/num.rs:284` | `shr(a, n)` |
| `num_bigint::biguint::shift::<BigUint as ShrAssign<u64>>::shr_assign` | 3 | 1 | `crates/zed-kernel/src/num/bound.rs:66` | `shr(a, n)` |
| `num_bigint::biguint::subtraction::<&BigUint as Sub<BigUint>>::sub` | 3 | 1 | `crates/zed-kernel/src/num.rs:1257` | `a - b` |
| `num_bigint::biguint::subtraction::<&BigUint as Sub<Self>>::sub` | 27 | 3 | `crates/zed-kernel/src/num.rs:1295` | `a - b` |
| `num_bigint::biguint::subtraction::<&BigUint as Sub<u32>>::sub` | 9 | 1 | `crates/zedc/src/store/int.rs:724` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as Sub<&BigUint>>::sub` | 3 | 1 | `crates/zed-kernel/src/types/empty.rs:2040` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as Sub<Self>>::sub` | 15 | 2 | `crates/zedc/src/store/int.rs:727` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as Sub<u64>>::sub` | 3 | 1 | `crates/zedc/src/store/int.rs:1460` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as Sub<u8>>::sub` | 3 | 1 | `crates/zedc/src/store/presburger/deep/canon.rs:440` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as SubAssign<&BigUint>>::sub_assign` | 3 | 1 | `crates/zedc/src/store/presburger/deep/canon.rs:550` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as SubAssign<u32>>::sub_assign` | 3 | 1 | `crates/zed-kernel/src/types/empty.rs:2079` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as SubAssign<u8>>::sub_assign` | 6 | 1 | `crates/zedc/src/store/presburger/deep/canon.rs:371` | `a - b` |
| `num_integer::<i128 as Integer>::div_floor` | 1 | 1 | `crates/zedc/src/store/int.rs:2155` | `a div b` |
| `num_integer::<i128 as Integer>::gcd` | 1 | 1 | `crates/zedc/src/store/int.rs:2243` | row STD-num |
| `num_integer::<i128 as Integer>::mod_floor` | 1 | 1 | `crates/zedc/src/store/int.rs:2205` | `a mod b` |
| `num_traits::cast::ToPrimitive::to_usize` | 3 | 2 | `crates/zed-kernel/src/num.rs:1279` | missing |
| `object::read::any::<Section<'data, 'file, R> as ObjectSection<'data>>::data` | 1 | 1 | `crates/zed-native/src/link.rs:237` | row S.4 |
| `object::read::any::File<'data, R>::parse` | 1 | 1 | `crates/zed-native/src/link.rs:234` | row S.4 |
| `object::read::archive::ArchiveFile<'data, R>::member` | 1 | 1 | `crates/zed-native/src/link.rs:259` | row S.4 |
| `object::read::archive::ArchiveFile<'data, R>::parse` | 1 | 1 | `crates/zed-native/src/link.rs:249` | row S.4 |
| `object::read::archive::ArchiveFile<'data, R>::symbols` | 1 | 1 | `crates/zed-native/src/link.rs:250` | row S.4 |
| `object::read::archive::ArchiveMember<'data>::file_range` | 1 | 1 | `crates/zed-native/src/link.rs:259` | row S.4 |
| `object::read::archive::ArchiveSymbol<'data>::name` | 1 | 1 | `crates/zed-native/src/link.rs:255` | row S.4 |
| `object::read::archive::ArchiveSymbol<'data>::offset` | 1 | 1 | `crates/zed-native/src/link.rs:259` | row S.4 |
| `object::read::read_cache::ReadCache<R>::new` | 2 | 1 | `crates/zed-native/src/link.rs:219` | row S.4 |
| `object::read::read_cache::ReadCache<R>::range` | 1 | 1 | `crates/zed-native/src/link.rs:260` | row S.4 |
| `object::read::traits::Object::section_by_name` | 1 | 1 | `crates/zed-native/src/link.rs:236` | row S.4 |
| `std::collections::hash::map::<HashMap<K, V, S, A> as Clone>::clone` | 7 | 1 | `crates/zedc/src/query.rs:130` | `x` |
| `std::collections::hash::map::<HashMap<K, V, S, A> as Index<&Q>>::index` | 88 | 17 | `crates/zed-kernel/src/provenance.rs:476` | `xs[i]` |
| `std::collections::hash::map::<HashMap<K, V, S, A> as IntoIterator>::into_iter` | 2 | 1 | `crates/zedc/src/check/mod.rs:2561` | row STD-seq |
| `std::collections::hash::map::<HashMap<K, V> as From<[(K, V); N]>>::from` | 4 | 2 | `crates/zed-kernel/src/types/bdd.rs:590` | missing |
| `std::collections::hash::map::Entry<'a, K, V, A>::or_insert` | 16 | 11 | `crates/zed-kernel/src/provenance.rs:406` | row STD-seq |
| `std::collections::hash::map::Entry<'a, K, V, A>::or_insert_with` | 12 | 10 | `crates/zed-kernel/src/eval.rs:423` | row STD-seq |
| `std::collections::hash::map::Entry<'a, K, V>::or_default` | 27 | 11 | `crates/zed-kernel/src/provenance.rs:291` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::clear` | 12 | 5 | `crates/zed-kernel/src/eval.rs:369` | row L6.13 |
| `std::collections::hash::map::HashMap<K, V, S, A>::contains_key` | 40 | 16 | `crates/zed-kernel/src/types/bdd.rs:319` | `k in m` |
| `std::collections::hash::map::HashMap<K, V, S, A>::entry` | 59 | 20 | `crates/zed-kernel/src/eval.rs:423` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::get` | 164 | 29 | `crates/zed-kernel/src/deep.rs:409` | `xs[i]` |
| `std::collections::hash::map::HashMap<K, V, S, A>::get_key_value` | 1 | 1 | `crates/zedc/src/zir/memory.rs:971` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::get_mut` | 6 | 4 | `crates/zed-kernel/src/types/debug.rs:93` | row L6.13 |
| `std::collections::hash::map::HashMap<K, V, S, A>::insert` | 121 | 30 | `crates/zed-kernel/src/deep.rs:400` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::is_empty` | 1 | 1 | `crates/zed-kernel/src/types/bdd.rs:1100` | `xs.count == 0` |
| `std::collections::hash::map::HashMap<K, V, S, A>::iter` | 1 | 1 | `crates/zed-kernel/src/types/bdd.rs:1031` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::keys` | 1 | 1 | `crates/zedc/src/store/presburger.rs:5797` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::len` | 16 | 8 | `crates/zed-kernel/src/types/empty.rs:2699` | `xs.count` |
| `std::collections::hash::map::HashMap<K, V, S, A>::remove` | 24 | 9 | `crates/zed-kernel/src/types/bdd.rs:593` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::values` | 1 | 1 | `crates/zed-kernel/src/types/empty.rs:2916` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V>::new` | 117 | 32 | `crates/zed-kernel/src/deep.rs:385` | `{}` |
| `std::collections::hash::map::HashMap<K, V>::with_capacity` | 3 | 3 | `crates/zed-kernel/src/types/bdd.rs:579` | row L6.13 |
| `std::collections::hash::map::OccupiedEntry<'a, K, V, A>::get` | 3 | 2 | `crates/zed-kernel/src/types/empty.rs:2709` | row STD-seq |
| `std::collections::hash::map::OccupiedEntry<'a, K, V, A>::get_mut` | 1 | 1 | `crates/zedc/src/check/mod.rs:1364` | row L6.13 |
| `std::collections::hash::map::VacantEntry<'a, K, V, A>::insert` | 4 | 3 | `crates/zed-kernel/src/types/empty.rs:2707` | row STD-seq |
| `std::collections::hash::map::VacantEntry<'a, K, V, A>::key` | 1 | 1 | `crates/zed-kernel/src/types/rec.rs:549` | missing |
| `std::collections::hash::set::<HashSet<T, S, A> as Clone>::clone` | 2 | 2 | `crates/zedc/src/check/mod.rs:2522` | `x` |
| `std::collections::hash::set::<HashSet<T, S, A> as Extend<T>>::extend` | 6 | 4 | `crates/zed-kernel/src/types/debug.rs:57` | row L6.13 |
| `std::collections::hash::set::HashSet<T, S, A>::contains` | 37 | 14 | `crates/zed-kernel/src/deep.rs:269` | `k in m` |
| `std::collections::hash::set::HashSet<T, S, A>::insert` | 73 | 24 | `crates/zed-kernel/src/deep.rs:273` | row STD-seq |
| `std::collections::hash::set::HashSet<T, S, A>::is_empty` | 2 | 2 | `crates/zedc/src/check/ty.rs:3331` | `xs.count == 0` |
| `std::collections::hash::set::HashSet<T, S, A>::iter` | 2 | 1 | `crates/zedc/src/check/ty.rs:2965` | row STD-seq |
| `std::collections::hash::set::HashSet<T, S, A>::len` | 1 | 1 | `crates/zedc/src/check/ty.rs:3338` | `xs.count` |
| `std::collections::hash::set::HashSet<T, S, A>::remove` | 4 | 2 | `crates/zedc/src/check/ty.rs:3356` | row STD-seq |
| `std::collections::hash::set::HashSet<T>::new` | 47 | 20 | `crates/zed-kernel/src/deep.rs:264` | `{}` |
| `std::env::args_os` | 1 | 1 | `crates/zedc/src/main.rs:18` | missing |
| `std::env::current_exe` | 2 | 1 | `crates/zed-native/src/link.rs:49` | missing |
| `std::env::var_os` | 2 | 1 | `crates/zed-native/src/link.rs:46` | missing |
| `std::f64::f64::powf` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2215` | missing |
| `std::ffi::os_str::<OsStr as ToOwned>::to_owned` | 1 | 1 | `crates/zed-native/src/link.rs:118` | `x` |
| `std::ffi::os_str::OsStr::to_str` | 3 | 2 | `crates/zedc/src/run.rs:886` | missing |
| `std::ffi::os_str::OsStr::to_string_lossy` | 3 | 2 | `crates/zed-native/src/exe.rs:155` | missing |
| `std::ffi::os_str::OsString::into_string` | 1 | 1 | `crates/zedc/src/main.rs:31` | missing |
| `std::ffi::os_str::OsString::push` | 1 | 1 | `crates/zed-native/src/link.rs:119` | row L6.13 |
| `std::fs::DirEntry::path` | 1 | 1 | `crates/zed-native/src/link.rs:166` | missing |
| `std::fs::File::open` | 2 | 1 | `crates/zed-native/src/link.rs:218` | missing |
| `std::fs::OpenOptions::create_new` | 1 | 1 | `crates/zed-native/src/link.rs:124` | missing |
| `std::fs::OpenOptions::new` | 1 | 1 | `crates/zed-native/src/link.rs:122` | missing |
| `std::fs::OpenOptions::open` | 1 | 1 | `crates/zed-native/src/link.rs:125` | missing |
| `std::fs::OpenOptions::write` | 1 | 1 | `crates/zed-native/src/link.rs:123` | missing |
| `std::fs::canonicalize` | 1 | 1 | `crates/zedc/src/unit.rs:821` | missing |
| `std::fs::read` | 7 | 4 | `crates/zedc/src/main.rs:41` | missing |
| `std::fs::read_dir` | 1 | 1 | `crates/zed-native/src/link.rs:165` | missing |
| `std::fs::remove_file` | 1 | 1 | `crates/zed-native/src/link.rs:138` | missing |
| `std::fs::write` | 2 | 1 | `crates/zedc/src/run.rs:1063` | missing |
| `std::hash::random::<DefaultHasher as Hasher>::finish` | 1 | 1 | `crates/zedc/src/store/presburger/deep.rs:740` | missing |
| `std::hash::random::DefaultHasher::new` | 1 | 1 | `crates/zedc/src/store/presburger/deep.rs:720` | missing |
| `std::io::stdio::<Stdout as Write>::flush` | 1 | 1 | `crates/zed-native/src/exe.rs:137` | missing |
| `std::io::stdio::stderr` | 4 | 2 | `crates/zed-native/src/exe.rs:145` | missing |
| `std::io::stdio::stdin` | 2 | 2 | `crates/zed-native/src/exe.rs:145` | missing |
| `std::io::stdio::stdout` | 4 | 2 | `crates/zed-native/src/exe.rs:137` | missing |
| `std::macros::eprintln!` | 5 | 2 | `crates/zedc/src/main.rs:35` | missing |
| `std::macros::panic!` | 10 | 6 | `crates/zed-kernel/src/provenance.rs:241` | row S.1d |
| `std::macros::print!` | 1 | 1 | `crates/zedc/src/main.rs:45` | missing |
| `std::macros::println!` | 1 | 1 | `crates/zedc/src/main.rs:39` | missing |
| `std::os::unix::ffi::os_str::<OsString as OsStringExt>::from_vec` | 1 | 1 | `crates/zed-native/src/exe.rs:131` | missing |
| `std::path::<PathBuf as Clone>::clone` | 1 | 1 | `crates/zedc/src/unit.rs:848` | `x` |
| `std::path::<PathBuf as From<OsString>>::from` | 2 | 1 | `crates/zed-native/src/link.rs:53` | missing |
| `std::path::Component<'a>::as_os_str` | 1 | 1 | `crates/zedc/src/unit.rs:828` | missing |
| `std::path::Path::ancestors` | 1 | 1 | `crates/zedc/src/unit.rs:860` | missing |
| `std::path::Path::as_os_str` | 1 | 1 | `crates/zed-native/src/link.rs:118` | missing |
| `std::path::Path::components` | 1 | 1 | `crates/zedc/src/unit.rs:827` | missing |
| `std::path::Path::display` | 17 | 2 | `crates/zed-native/src/link.rs:90` | missing |
| `std::path::Path::file_name` | 1 | 1 | `crates/zed-native/src/link.rs:167` | missing |
| `std::path::Path::is_file` | 2 | 2 | `crates/zed-native/src/link.rs:84` | missing |
| `std::path::Path::join` | 3 | 1 | `crates/zedc/src/unit.rs:73` | row STD-text |
| `std::path::Path::new` | 2 | 2 | `crates/zed-native/src/link.rs:64` | missing |
| `std::path::Path::parent` | 3 | 1 | `crates/zedc/src/unit.rs:822` | missing |
| `std::path::Path::strip_prefix` | 1 | 1 | `crates/zedc/src/unit.rs:825` | row STD-text |
| `std::path::Path::to_path_buf` | 1 | 1 | `crates/zedc/src/unit.rs:831` | missing |
| `std::path::Path::with_file_name` | 1 | 1 | `crates/zed-native/src/link.rs:50` | missing |
| `std::process::<ExitCode as From<u8>>::from` | 5 | 1 | `crates/zedc/src/main.rs:22` | missing |
| `std::process::Command::arg` | 5 | 1 | `crates/zed-native/src/link.rs:129` | missing |
| `std::process::Command::args` | 1 | 1 | `crates/zed-native/src/link.rs:133` | missing |
| `std::process::Command::new` | 1 | 1 | `crates/zed-native/src/link.rs:128` | missing |
| `std::process::Command::output` | 1 | 1 | `crates/zed-native/src/link.rs:137` | missing |
| `std::process::ExitStatus::success` | 1 | 1 | `crates/zed-native/src/link.rs:146` | missing |
| `std::sync::lazy_lock::LazyLock<T, F>::new` | 2 | 1 | `crates/zed-kernel/src/types/rec.rs:89` | missing |
| `std::sync::once_lock::OnceLock<T>::get` | 8 | 4 | `crates/zed-kernel/src/types.rs:1590` | missing |
| `std::sync::once_lock::OnceLock<T>::get_or_init` | 11 | 8 | `crates/zed-kernel/src/types.rs:250` | missing |
| `std::sync::once_lock::OnceLock<T>::new` | 10 | 6 | `crates/zed-kernel/src/types.rs:491` | missing |
| `std::sync::once_lock::OnceLock<T>::set` | 5 | 3 | `crates/zed-kernel/src/types.rs:1629` | missing |
| `std::sync::once_lock::OnceLock<T>::take` | 2 | 2 | `crates/zed-kernel/src/types.rs:183` | row L6.13 |
| `std::sync::poison::PoisonError<T>::into_inner` | 1 | 1 | `crates/zedc/src/store/int.rs:346` | `x` |
| `std::sync::poison::mutex::<Mutex<T> as Default>::default` | 1 | 1 | `crates/zedc/src/stage.rs:1879` | missing |
| `std::sync::poison::mutex::<MutexGuard<'_, T> as Deref>::deref` | 1 | 1 | `crates/zedc/src/store/int.rs:853` | `x` |
| `std::sync::poison::mutex::<MutexGuard<'_, T> as DerefMut>::deref_mut` | 3 | 2 | `crates/zedc/src/stage.rs:1639` | `x` |
| `std::sync::poison::mutex::Mutex<T>::lock` | 9 | 3 | `crates/zed-kernel/src/types/rec.rs:362` | missing |
| `std::thread::functions::spawn` | 3 | 2 | `crates/zed-kernel/src/types/bdd.rs:2291` | missing |
| `std::thread::local::LocalKey<Cell<T>>::get` | 6 | 4 | `crates/zed-kernel/src/deep.rs:289` | missing |
| `std::thread::local::LocalKey<Cell<T>>::replace` | 4 | 4 | `crates/zed-kernel/src/num.rs:1338` | row L6.13 |
| `std::thread::local::LocalKey<Cell<T>>::set` | 7 | 4 | `crates/zed-kernel/src/deep.rs:292` | missing |
| `std::thread::local::LocalKey<Cell<T>>::take` | 3 | 1 | `crates/zed-kernel/src/num.rs:1339` | row L6.13 |
| `std::thread::local::LocalKey<RefCell<T>>::set` | 1 | 1 | `crates/zedc/src/check/ty.rs:3715` | missing |
| `std::thread::local::LocalKey<RefCell<T>>::take` | 1 | 1 | `crates/zedc/src/check/ty.rs:3720` | row L6.13 |
| `std::thread::local::LocalKey<RefCell<T>>::with_borrow` | 1 | 1 | `crates/zed-kernel/src/types.rs:1627` | missing |
| `std::thread::local::LocalKey<RefCell<T>>::with_borrow_mut` | 11 | 3 | `crates/zed-kernel/src/deep.rs:168` | missing |
| `std::thread::local::LocalKey<T>::try_with` | 5 | 2 | `crates/zed-kernel/src/deep.rs:68` | missing |
| `std::thread::local::LocalKey<T>::with` | 26 | 8 | `crates/zed-kernel/src/family.rs:47` | missing |
| `std::thread::local::thread_local!` | 22 | 14 | `crates/zed-kernel/src/deep.rs:32` | missing |
| `unicode_ident::is_xid_continue` | 13 | 4 | `crates/zedc/src/lex/name.rs:16` | row S.1c |
| `unicode_ident::is_xid_start` | 5 | 3 | `crates/zedc/src/lex/name.rs:16` | row S.1c |
| `unicode_normalization::<&'a str as UnicodeNormalization<Chars<'a>>>::nfc` | 1 | 1 | `crates/zedc/src/source.rs:126` | row S.1c |
| `unicode_normalization::lookups::canonical_combining_class` | 2 | 1 | `crates/zedc/src/source.rs:14` | row S.1c |
| `unicode_normalization::quick_check::is_nfc` | 4 | 1 | `crates/zedc/src/source.rs:15` | row S.1c |
| `unicode_script::<ScriptExtension as From<Script>>::from` | 1 | 1 | `crates/zedc/src/lex/name.rs:65` | row S.1c |
| `unicode_script::<char as UnicodeScript>::script` | 1 | 1 | `crates/zedc/src/lex/name.rs:78` | row S.1c |
| `unicode_script::<char as UnicodeScript>::script_extension` | 1 | 1 | `crates/zedc/src/lex/name.rs:69` | row S.1c |
| `unicode_script::Script::full_name` | 1 | 1 | `crates/zedc/src/lex/name.rs:84` | row S.1c |
| `unicode_script::ScriptExtension::for_str` | 1 | 1 | `crates/zedc/src/lex/name.rs:59` | row S.1c |
| `unicode_script::ScriptExtension::intersection` | 1 | 1 | `crates/zedc/src/lex/name.rs:69` | row S.1c |
| `unicode_script::ScriptExtension::is_empty` | 2 | 1 | `crates/zedc/src/lex/name.rs:59` | row S.1c |
| `unicode_script::ScriptExtension::union` | 1 | 1 | `crates/zedc/src/lex/name.rs:66` | row S.1c |
