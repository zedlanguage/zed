# Routines the Rust calls

Plan row PORT-catalog. Every function, method, operator and macro of the Rust standard library or of a dependency that the code of `zedc`, `zed-kernel` and `zed-native` calls, outside unit tests (`#[cfg(test)]`), with what stands for it in Zed. Step S.1 regenerates it over the Rust of its time, and the standard library rows STD-seq, STD-text and STD-num start from it.

The tool `catalog` of `zed-tools` writes the first four columns from a SCIP index that `rust-analyzer scip` makes of this repository, in which every call is resolved to the routine it reaches, operators and trait methods included:

    zrun build/cargo/debug/catalog ../zed zed/compiler/CATALOG.md --write   # regenerate, keeping the Zed column
    zrun build/cargo/debug/catalog ../zed zed/compiler/CATALOG.md           # check

A routine is named `package::module::Type::name`, with an impl's self type and trait written `<T as Trait>`; one Rust routine per row, so `+` on `u32`, on `&u32` and on `BigInt` are three rows. *Uses* counts the call sites, *Files* the files holding them, and *First use* is the first site by path and line.

The Zed column is written by hand and is one of:

- `missing`: nothing in Zed or in the plan provides the routine yet;
- `row ID`: plan rows of `docs/plan_dag.md` that provide it, separated by commas;
- Zed texts in backticks: expressions of the grammar of DESIGN.md whose defined words lie in the bootstrap subset (layer 24 or below; ZED0.md), with `a`, `b`, `n`, `i`, `x`, `xs`, `ys`, `s`, `t`, `m`, `k`, `f`, `p` and `z` standing for the operands. A text is exact: where Zed and Rust differ, it writes out Rust's result (a truncating `/` on signed integers, a wrapping or saturating operation, a fixed `width:`). `x` alone marks a routine with no work in Zed: a copy, a borrow, a dereference or a shared pointer, which Zed's immutable values make the value itself.

The tool checks every row against the index, so a routine called and not listed, or listed and no longer called, is an error, and checks each Zed column against the grammar, the words table and the plan: each name in a text is an operand, a lambda parameter or a defined word, and each call of a word passes the arguments the word takes (a `width:` where one is required, sort keys or `by:` to `sort`). `missing` entries are allowed until S.1, whose test is that none is left. Plan rows used: STD-seq, STD-text, STD-num and STD-blake3 (the seed library), S.1c (Unicode tables), S.1d (`#bug` for broken invariants), L5.8a (ranges of an ordered family and the priority queue), L6.13 (reuse in place, which replaces capacity and in-place mutation), S.4 (the MLIR text emitter, which replaces Cranelift, `object` and `libc`).

Counts: 1495 routines, 57704 uses.

| Routine | Uses | Files | First use | Zed |
|---|--:|--:|---|---|
| `alloc::borrow::<Cow<'_, B> as Clone>::clone` | 2 | 2 | `crates/zed-kernel/src/bits.rs:248` | `x` |
| `alloc::borrow::<Cow<'_, B> as Deref>::deref` | 33 | 7 | `crates/zed-kernel/src/bits.rs:129` | `x` |
| `alloc::borrow::<Cow<'_, B> as Ord>::cmp` | 2 | 1 | `crates/zed-kernel/src/num.rs:1444` | missing |
| `alloc::borrow::Cow<'_, B>::into_owned` | 11 | 6 | `crates/zed-kernel/src/bits.rs:248` | `x` |
| `alloc::boxed::<Box<T, A> as Clone>::clone` | 4 | 2 | `crates/zedc-check/src/check/walk.rs:2123` | `x` |
| `alloc::boxed::<Box<T, A> as Deref>::deref` | 75 | 13 | `crates/zed-kernel/src/eval.rs:774` | `x` |
| `alloc::boxed::<Box<T, A> as Ord>::cmp` | 2 | 1 | `crates/zedc-int/src/int.rs:259` | missing |
| `alloc::boxed::<Box<T, A> as PartialEq<Self>>::eq` | 3 | 1 | `crates/zed-kernel/src/num.rs:1500` | `a == b` |
| `alloc::boxed::<Box<[T], A> as Clone>::clone` | 1 | 1 | `crates/zed-kernel/src/num.rs:610` | `x` |
| `alloc::boxed::<Box<[T]> as Default>::default` | 1 | 1 | `crates/zed-kernel/src/num.rs:68` | `[]` |
| `alloc::boxed::<Box<str, A> as Clone>::clone` | 1 | 1 | `crates/zedc-base/src/work.rs:259` | missing |
| `alloc::boxed::Box<T>::new` | 119 | 19 | `crates/zed-kernel/src/eval.rs:1037` | `x` |
| `alloc::boxed::Box<T>::pin` | 3 | 2 | `crates/zed-kernel/src/frames.rs:51` | missing |
| `alloc::collections::binary_heap::BinaryHeap<T, A>::clear` | 1 | 1 | `crates/zedc-solvers/src/negsssp.rs:198` | row L6.13 |
| `alloc::collections::binary_heap::BinaryHeap<T, A>::peek` | 1 | 1 | `crates/zedc-solvers/src/negsssp.rs:214` | row L5.8a |
| `alloc::collections::binary_heap::BinaryHeap<T, A>::pop` | 8 | 4 | `crates/zedc-lattice/src/interval.rs:287` | row L5.8a |
| `alloc::collections::binary_heap::BinaryHeap<T, A>::push` | 11 | 4 | `crates/zedc-lattice/src/interval.rs:297` | row L6.13 |
| `alloc::collections::binary_heap::BinaryHeap<T>::new` | 2 | 2 | `crates/zedc-presburger/src/presburger.rs:7376` | row L5.8a |
| `alloc::collections::btree::map::<BTreeMap<K, V, A> as Clone>::clone` | 40 | 12 | `crates/zed-kernel/src/term/walk.rs:53` | `x` |
| `alloc::collections::btree::map::<BTreeMap<K, V, A> as Extend<(K, V)>>::extend` | 5 | 3 | `crates/zed-kernel/src/types/empty.rs:288` | row L6.13 |
| `alloc::collections::btree::map::<BTreeMap<K, V, A> as Index<&Q>>::index` | 142 | 14 | `crates/zed-kernel/src/eval.rs:262` | `xs[i]` |
| `alloc::collections::btree::map::<BTreeMap<K, V, A> as IntoIterator>::into_iter` | 20 | 11 | `crates/zed-kernel/src/eval.rs:1572` | row STD-seq |
| `alloc::collections::btree::map::<BTreeMap<K, V, A> as PartialEq<Self>>::eq` | 18 | 3 | `crates/zedc-lattice/src/affine.rs:202` | `a == b` |
| `alloc::collections::btree::map::<BTreeMap<K, V> as From<[(K, V); N]>>::from` | 5 | 5 | `crates/zed-kernel/src/provenance.rs:324` | missing |
| `alloc::collections::btree::map::<Iter<'a, K, V> as Iterator>::next` | 10 | 3 | `crates/zedc-preimage/src/preimage.rs:1174` | row STD-seq |
| `alloc::collections::btree::map::<Keys<'a, K, V> as Iterator>::next` | 1 | 1 | `crates/zedc-presburger/src/hull.rs:276` | row STD-seq |
| `alloc::collections::btree::map::<Range<'a, K, V> as Iterator>::next` | 4 | 2 | `crates/zed-kernel/src/types/bdd.rs:1918` | row L5.8a |
| `alloc::collections::btree::map::<Values<'a, K, V> as Iterator>::next` | 1 | 1 | `crates/zedc-presburger/src/hull.rs:247` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::clear` | 6 | 2 | `crates/zed-kernel/src/types/empty.rs:266` | row L6.13 |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::contains_key` | 38 | 12 | `crates/zed-kernel/src/eval.rs:888` | `k in m` |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::entry` | 60 | 18 | `crates/zed-kernel/src/eval.rs:1424` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::get` | 156 | 31 | `crates/zed-kernel/src/eval.rs:886` | `xs[i]` |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::get_key_value` | 3 | 2 | `crates/zed-native/src/tables.rs:151` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::get_mut` | 9 | 7 | `crates/zed-kernel/src/eval.rs:1191` | row L6.13 |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::insert` | 121 | 25 | `crates/zed-kernel/src/eval.rs:232` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::into_keys` | 2 | 2 | `crates/zedc-preimage/src/product.rs:2434` | missing |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::into_values` | 8 | 5 | `crates/zed-kernel/src/types/empty.rs:3938` | missing |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::is_empty` | 36 | 10 | `crates/zed-kernel/src/types.rs:175` | `xs.count == 0` |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::iter` | 74 | 16 | `crates/zed-kernel/src/print.rs:335` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::iter_mut` | 1 | 1 | `crates/zedc-types/src/ty.rs:470` | row L6.13 |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::keys` | 64 | 11 | `crates/zed-kernel/src/types.rs:1488` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::len` | 24 | 11 | `crates/zed-kernel/src/types/empty.rs:2364` | `xs.count` |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::pop_last` | 2 | 2 | `crates/zed-kernel/src/provenance.rs:326` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::range` | 6 | 3 | `crates/zed-kernel/src/types/bdd.rs:1914` | row L5.8a |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::remove` | 30 | 15 | `crates/zed-kernel/src/eval.rs:1817` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::retain` | 4 | 4 | `crates/zed-kernel/src/types/empty.rs:1315` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::values` | 35 | 9 | `crates/zed-kernel/src/types.rs:876` | row STD-seq |
| `alloc::collections::btree::map::BTreeMap<K, V, A>::values_mut` | 2 | 1 | `crates/zedc-check/src/check/mod.rs:2612` | row L6.13 |
| `alloc::collections::btree::map::BTreeMap<K, V>::new` | 128 | 25 | `crates/zed-kernel/src/eval.rs:1567` | `{}` |
| `alloc::collections::btree::map::entry::Entry<'a, K, V, A>::and_modify` | 1 | 1 | `crates/zedc-resolve/src/resolve.rs:233` | row STD-seq |
| `alloc::collections::btree::map::entry::Entry<'a, K, V, A>::or_default` | 28 | 12 | `crates/zed-kernel/src/eval.rs:1424` | row STD-seq |
| `alloc::collections::btree::map::entry::Entry<'a, K, V, A>::or_insert` | 18 | 7 | `crates/zed-kernel/src/types/empty.rs:892` | row STD-seq |
| `alloc::collections::btree::map::entry::Entry<'a, K, V, A>::or_insert_with` | 11 | 7 | `crates/zed-kernel/src/types.rs:2741` | row STD-seq |
| `alloc::collections::btree::map::entry::OccupiedEntry<'a, K, V, A>::get` | 1 | 1 | `crates/zedc-zir/src/zir/lower.rs:432` | row STD-seq |
| `alloc::collections::btree::map::entry::VacantEntry<'a, K, V, A>::insert` | 3 | 2 | `crates/zed-kernel/src/value.rs:833` | row STD-seq |
| `alloc::collections::btree::set::<BTreeSet<T, A> as Clone>::clone` | 10 | 3 | `crates/zedc-check/src/check/mod.rs:3535` | `x` |
| `alloc::collections::btree::set::<BTreeSet<T, A> as Debug>::fmt` | 1 | 1 | `crates/zedc-lattice/src/cell.rs:173` | missing |
| `alloc::collections::btree::set::<BTreeSet<T, A> as Extend<T>>::extend` | 52 | 11 | `crates/zed-kernel/src/types.rs:2605` | row L6.13 |
| `alloc::collections::btree::set::<BTreeSet<T, A> as IntoIterator>::into_iter` | 34 | 9 | `crates/zed-kernel/src/eval.rs:1842` | row STD-seq |
| `alloc::collections::btree::set::<BTreeSet<T, A> as PartialEq<Self>>::eq` | 3 | 1 | `crates/zedc-lattice/src/cell.rs:160` | `a == b` |
| `alloc::collections::btree::set::<BTreeSet<T> as From<[T; N]>>::from` | 6 | 5 | `crates/zed-kernel/src/provenance.rs:308` | missing |
| `alloc::collections::btree::set::<Iter<'a, T> as Iterator>::next` | 3 | 2 | `crates/zedc-preimage/src/product.rs:180` | row STD-seq |
| `alloc::collections::btree::set::<Range<'a, T> as DoubleEndedIterator>::next_back` | 1 | 1 | `crates/zedc-lattice/src/interval.rs:512` | missing |
| `alloc::collections::btree::set::<Range<'a, T> as Iterator>::next` | 1 | 1 | `crates/zedc-lattice/src/interval.rs:517` | row L5.8a |
| `alloc::collections::btree::set::BTreeSet<T, A>::clear` | 1 | 1 | `crates/zedc-types/src/ty.rs:3540` | row L6.13 |
| `alloc::collections::btree::set::BTreeSet<T, A>::contains` | 75 | 16 | `crates/zed-kernel/src/eval.rs:1389` | `k in m` |
| `alloc::collections::btree::set::BTreeSet<T, A>::first` | 6 | 3 | `crates/zedc-presburger/src/conjuncts.rs:228` | `xs.first` |
| `alloc::collections::btree::set::BTreeSet<T, A>::get` | 1 | 1 | `crates/zed-kernel/src/provenance.rs:508` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::insert` | 97 | 15 | `crates/zed-kernel/src/eval.rs:1759` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::intersection` | 3 | 2 | `crates/zedc-lattice/src/affine.rs:503` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::is_empty` | 43 | 8 | `crates/zed-kernel/src/types/empty.rs:1323` | `xs.count == 0` |
| `alloc::collections::btree::set::BTreeSet<T, A>::iter` | 88 | 15 | `crates/zed-kernel/src/types/empty.rs:1328` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::len` | 10 | 5 | `crates/zed-kernel/src/types.rs:2566` | `xs.count` |
| `alloc::collections::btree::set::BTreeSet<T, A>::pop_first` | 2 | 2 | `crates/zed-kernel/src/types/empty.rs:1706` | missing |
| `alloc::collections::btree::set::BTreeSet<T, A>::pop_last` | 2 | 1 | `crates/zedc-stage/src/stage.rs:1959` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::range` | 6 | 3 | `crates/zedc-lattice/src/affine.rs:437` | row L5.8a |
| `alloc::collections::btree::set::BTreeSet<T, A>::remove` | 20 | 6 | `crates/zed-kernel/src/eval.rs:1753` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::retain` | 2 | 2 | `crates/zed-kernel/src/types/empty.rs:3886` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T, A>::union` | 1 | 1 | `crates/zedc-lattice/src/lattice.rs:256` | row STD-seq |
| `alloc::collections::btree::set::BTreeSet<T>::new` | 85 | 15 | `crates/zed-kernel/src/provenance.rs:304` | `{}` |
| `alloc::collections::vec_deque::<VecDeque<T, A> as IntoIterator>::into_iter` | 1 | 1 | `crates/zedc-check/src/check/mod.rs:2875` | missing |
| `alloc::collections::vec_deque::<VecDeque<T> as From<[T; N]>>::from` | 2 | 1 | `crates/zedc-check/src/check/walk.rs:755` | missing |
| `alloc::collections::vec_deque::VecDeque<T, A>::append` | 1 | 1 | `crates/zedc-check/src/check/mod.rs:396` | missing |
| `alloc::collections::vec_deque::VecDeque<T, A>::back` | 1 | 1 | `crates/zedc-syntax/src/ast/mod.rs:285` | `xs.last` |
| `alloc::collections::vec_deque::VecDeque<T, A>::front` | 1 | 1 | `crates/zedc-check/src/check/arms.rs:703` | missing |
| `alloc::collections::vec_deque::VecDeque<T, A>::get_mut` | 1 | 1 | `crates/zedc-syntax/src/ast/mod.rs:369` | row L6.13 |
| `alloc::collections::vec_deque::VecDeque<T, A>::is_empty` | 1 | 1 | `crates/zedc-preimage/src/product.rs:2047` | `xs.count == 0` |
| `alloc::collections::vec_deque::VecDeque<T, A>::iter` | 2 | 2 | `crates/zedc-check/src/check/mod.rs:2858` | row STD-seq |
| `alloc::collections::vec_deque::VecDeque<T, A>::len` | 2 | 1 | `crates/zedc-check/src/check/mod.rs:395` | missing |
| `alloc::collections::vec_deque::VecDeque<T, A>::pop_back` | 2 | 2 | `crates/zedc-check/src/check/mod.rs:399` | row STD-seq |
| `alloc::collections::vec_deque::VecDeque<T, A>::pop_front` | 5 | 3 | `crates/zedc-check/src/check/arms.rs:678` | row STD-seq |
| `alloc::collections::vec_deque::VecDeque<T, A>::push_back` | 4 | 3 | `crates/zedc-check/src/check/arms.rs:769` | row L6.13 |
| `alloc::collections::vec_deque::VecDeque<T, A>::push_front` | 2 | 2 | `crates/zedc-check/src/check/mod.rs:400` | missing |
| `alloc::collections::vec_deque::VecDeque<T>::new` | 8 | 3 | `crates/zedc-check/src/check/walk.rs:745` | `[]` |
| `alloc::io::read::Read::read_to_end` | 1 | 1 | `crates/zedc/src/run.rs:966` | missing |
| `alloc::macros::format!` | 902 | 67 | `crates/zed-kernel/src/bits.rs:51` | `"${x}"` |
| `alloc::macros::vec!` | 1102 | 93 | `crates/zed-kernel/src/eval.rs:368` | missing |
| `alloc::rc::<Rc<T, A> as AsRef<T>>::as_ref` | 1 | 1 | `crates/zedc-check/src/check/walk.rs:2158` | `x` |
| `alloc::rc::<Rc<T, A> as Clone>::clone` | 49 | 9 | `crates/zed-kernel/src/eval.rs:834` | `x` |
| `alloc::rc::<Rc<T, A> as Deref>::deref` | 36 | 4 | `crates/zedc-check/src/check/mod.rs:1032` | `x` |
| `alloc::rc::<Rc<T, A> as PartialOrd<Self>>::lt` | 6 | 1 | `crates/zedc-presburger/src/presburger.rs:5168` | `a < b` |
| `alloc::rc::<Rc<T> as Default>::default` | 1 | 1 | `crates/zed-kernel/src/eval.rs:379` | missing |
| `alloc::rc::Rc<T, A>::as_ptr` | 1 | 1 | `crates/zedc-presburger/src/presburger.rs:7004` | missing |
| `alloc::rc::Rc<T, A>::ptr_eq` | 2 | 1 | `crates/zedc-preimage/src/preimage.rs:4676` | row L6.13 |
| `alloc::rc::Rc<T, A>::try_unwrap` | 3 | 3 | `crates/zedc-check/src/check/mod.rs:538` | row L6.13 |
| `alloc::rc::Rc<T>::new` | 45 | 9 | `crates/zed-kernel/src/eval.rs:829` | `x` |
| `alloc::slice::[T]::concat` | 11 | 6 | `crates/zed-kernel/src/num.rs:159` | row STD-seq |
| `alloc::slice::[T]::join` | 75 | 34 | `crates/zed-kernel/src/bits.rs:82` | row STD-text |
| `alloc::slice::[T]::sort` | 17 | 9 | `crates/zed-kernel/src/eval.rs:1821` | `xs.sort(asc x -> x)` |
| `alloc::slice::[T]::sort_by` | 16 | 12 | `crates/zed-kernel/src/value.rs:392` | `xs.sort(by: f)` |
| `alloc::slice::[T]::sort_by_cached_key` | 1 | 1 | `crates/zedc-zir/src/zir/text.rs:382` | `xs.sort(asc f)` |
| `alloc::slice::[T]::sort_by_key` | 21 | 11 | `crates/zedc-check/src/check/mod.rs:1658` | `xs.sort(asc f)` |
| `alloc::slice::[T]::to_vec` | 53 | 27 | `crates/zed-kernel/src/eval.rs:937` | `x` |
| `alloc::str::<str as ToOwned>::to_owned` | 1 | 1 | `crates/zedc-presburger/src/presburger.rs:1377` | `x` |
| `alloc::str::str::repeat` | 9 | 4 | `crates/zed-kernel/src/num.rs:1352` | row STD-text |
| `alloc::str::str::replace` | 4 | 2 | `crates/zedc-base/src/source.rs:129` | row L6.13 |
| `alloc::str::str::to_lowercase` | 1 | 1 | `crates/zed-kernel/src/words.rs:194` | `lower(s)` |
| `alloc::string::<&str as PartialEq<String>>::ne` | 3 | 1 | `crates/zedc-zir/src/zir/text.rs:367` | `a != b` |
| `alloc::string::<String as AddAssign<&str>>::add_assign` | 15 | 1 | `crates/zed-kernel/src/print.rs:831` | `s ++ t` |
| `alloc::string::<String as Clone>::clone` | 50 | 16 | `crates/zed-kernel/src/types/print.rs:960` | `x` |
| `alloc::string::<String as Deref>::deref` | 5 | 2 | `crates/zedc-check/src/check/walk.rs:2020` | `x` |
| `alloc::string::<String as Extend<char>>::extend` | 2 | 2 | `crates/zed-kernel/src/num/fast.rs:1208` | missing |
| `alloc::string::<String as From<&str>>::from` | 4 | 3 | `crates/zed-native/src/tables.rs:311` | `x` |
| `alloc::string::<String as Index<I>>::index` | 6 | 3 | `crates/zedc-check/src/check/read.rs:61` | `fromUtf8(utf8(s).slice(a..<b))` |
| `alloc::string::<String as Ord>::cmp` | 4 | 4 | `crates/zed-kernel/src/types/rec.rs:998` | missing |
| `alloc::string::<String as PartialEq<&str>>::eq` | 27 | 9 | `crates/zed-kernel/src/num.rs:1536` | `a == b` |
| `alloc::string::<T as ToString>::to_string` | 181 | 54 | `crates/zed-kernel/src/eval.rs:891` | `"${x}"` |
| `alloc::string::String::as_bytes` | 16 | 9 | `crates/zed-kernel/src/types.rs:149` | `utf8(s)` |
| `alloc::string::String::as_str` | 84 | 28 | `crates/zed-kernel/src/text.rs:584` | `x` |
| `alloc::string::String::clear` | 1 | 1 | `crates/zed-native/src/tables.rs:215` | row L6.13 |
| `alloc::string::String::from_utf8` | 3 | 2 | `crates/zed-kernel/src/words.rs:266` | `fromUtf8(b)` |
| `alloc::string::String::from_utf8_lossy` | 3 | 2 | `crates/zed-native/src/link.rs:245` | missing |
| `alloc::string::String::into_bytes` | 1 | 1 | `crates/zedc/src/rows.rs:70` | `utf8(s)` |
| `alloc::string::String::is_empty` | 6 | 5 | `crates/zedc-elab/src/elab/walk.rs:1852` | `len(s) == 0` |
| `alloc::string::String::len` | 21 | 13 | `crates/zed-kernel/src/num.rs:1609` | `utf8(s).count` |
| `alloc::string::String::new` | 43 | 28 | `crates/zed-kernel/src/print.rs:34` | `""` |
| `alloc::string::String::push` | 13 | 6 | `crates/zed-kernel/src/types/print.rs:982` | row L6.13 |
| `alloc::string::String::push_str` | 48 | 16 | `crates/zed-kernel/src/num.rs:1352` | `s ++ t` |
| `alloc::string::String::truncate` | 7 | 3 | `crates/zedc-zir/src/zir/lower.rs:1738` | row L6.13 |
| `alloc::string::String::try_reserve_exact` | 5 | 4 | `crates/zed-kernel/src/text.rs:209` | row L6.13 |
| `alloc::string::String::with_capacity` | 4 | 4 | `crates/zed-kernel/src/num/fast.rs:1195` | row L6.13 |
| `alloc::sync::<Arc<T, A> as AsRef<T>>::as_ref` | 4 | 2 | `crates/zedc-check/src/check/mod.rs:2826` | `x` |
| `alloc::sync::<Arc<T, A> as Clone>::clone` | 593 | 45 | `crates/zed-kernel/src/eval.rs:889` | `x` |
| `alloc::sync::<Arc<T, A> as Deref>::deref` | 148 | 40 | `crates/zed-kernel/src/eval.rs:886` | `x` |
| `alloc::sync::<Arc<T, A> as Ord>::cmp` | 9 | 4 | `crates/zed-kernel/src/types/bdd.rs:1880` | missing |
| `alloc::sync::<Arc<T, A> as PartialEq<Self>>::eq` | 39 | 9 | `crates/zed-kernel/src/eval.rs:2011` | `a == b` |
| `alloc::sync::<Arc<T, A> as PartialEq<Self>>::ne` | 9 | 3 | `crates/zed-kernel/src/types/empty.rs:1496` | `a != b` |
| `alloc::sync::<Arc<[T], A> as From<Vec<T, A>>>::from` | 2 | 1 | `crates/zed-kernel/src/types.rs:1652` | `x` |
| `alloc::sync::<Arc<[T]> as From<[T; N]>>::from` | 1 | 1 | `crates/zedc/src/run.rs:330` | `x` |
| `alloc::sync::<Arc<str> as From<&str>>::from` | 11 | 8 | `crates/zed-kernel/src/term.rs:531` | `x` |
| `alloc::sync::<Arc<str> as From<String>>::from` | 4 | 4 | `crates/zed-kernel/src/text.rs:578` | `x` |
| `alloc::sync::Arc<T, A>::as_ptr` | 16 | 6 | `crates/zed-kernel/src/types.rs:517` | missing |
| `alloc::sync::Arc<T, A>::downgrade` | 8 | 6 | `crates/zed-kernel/src/types.rs:359` | missing |
| `alloc::sync::Arc<T, A>::get_mut` | 9 | 6 | `crates/zed-kernel/src/term.rs:371` | row L6.13 |
| `alloc::sync::Arc<T, A>::into_inner` | 5 | 3 | `crates/zed-kernel/src/provenance.rs:92` | `x` |
| `alloc::sync::Arc<T, A>::make_mut` | 5 | 2 | `crates/zed-kernel/src/term.rs:354` | row L6.13 |
| `alloc::sync::Arc<T, A>::ptr_eq` | 19 | 8 | `crates/zed-kernel/src/provenance.rs:105` | row L6.13 |
| `alloc::sync::Arc<T, A>::strong_count` | 5 | 4 | `crates/zed-kernel/src/term.rs:366` | row L6.13 |
| `alloc::sync::Arc<T, A>::try_unwrap` | 1 | 1 | `crates/zedc-lattice/src/cell.rs:145` | row L6.13 |
| `alloc::sync::Arc<T, A>::unwrap_or_clone` | 3 | 3 | `crates/zed-kernel/src/term.rs:361` | `x` |
| `alloc::sync::Arc<T>::new` | 88 | 28 | `crates/zed-kernel/src/provenance.rs:53` | `x` |
| `alloc::sync::Weak<T, A>::as_ptr` | 5 | 5 | `crates/zed-kernel/src/types.rs:334` | missing |
| `alloc::sync::Weak<T, A>::strong_count` | 2 | 2 | `crates/zed-kernel/src/types.rs:351` | missing |
| `alloc::sync::Weak<T, A>::upgrade` | 8 | 6 | `crates/zed-kernel/src/types.rs:352` | missing |
| `alloc::sync::Weak<T>::new` | 1 | 1 | `crates/zed-kernel/src/types/bdd.rs:741` | missing |
| `alloc::vec::<Vec<T, A> as Clone>::clone` | 79 | 27 | `crates/zed-kernel/src/eval.rs:1486` | `x` |
| `alloc::vec::<Vec<T, A> as Clone>::clone_from` | 2 | 1 | `crates/zed-kernel/src/types/bes.rs:792` | `x` |
| `alloc::vec::<Vec<T, A> as Deref>::deref` | 2 | 2 | `crates/zedc-presburger/src/presburger.rs:5610` | `x` |
| `alloc::vec::<Vec<T, A> as Extend<&'a T>>::extend` | 3 | 3 | `crates/zed-kernel/src/types.rs:2256` | row L6.13 |
| `alloc::vec::<Vec<T, A> as Extend<T>>::extend` | 615 | 66 | `crates/zed-kernel/src/deep.rs:32` | row L6.13 |
| `alloc::vec::<Vec<T, A> as Index<I>>::index` | 3324 | 69 | `crates/zed-kernel/src/eval.rs:424` | `xs[i]` |
| `alloc::vec::<Vec<T, A> as IndexMut<I>>::index_mut` | 1196 | 51 | `crates/zed-kernel/src/num/fast.rs:448` | row L6.13 |
| `alloc::vec::<Vec<T, A> as IntoIterator>::into_iter` | 320 | 62 | `crates/zed-kernel/src/eval.rs:815` | row STD-seq |
| `alloc::vec::<Vec<T, A> as Ord>::cmp` | 3 | 3 | `crates/zed-kernel/src/types/rec.rs:998` | missing |
| `alloc::vec::<Vec<T> as FromIterator<T>>::from_iter` | 1 | 1 | `crates/zedc-presburger/src/presburger.rs:6205` | `x` |
| `alloc::vec::<[T; N] as TryFrom<Vec<T, A>>>::try_from` | 7 | 5 | `crates/zed-kernel/src/eval.rs:1370` | missing |
| `alloc::vec::Vec<T, A>::append` | 16 | 10 | `crates/zed-kernel/src/value.rs:947` | row L6.13 |
| `alloc::vec::Vec<T, A>::as_slice` | 31 | 15 | `crates/zed-kernel/src/eval.rs:2188` | `x` |
| `alloc::vec::Vec<T, A>::capacity` | 2 | 2 | `crates/zedc-zir/src/canon/serial.rs:41` | missing |
| `alloc::vec::Vec<T, A>::clear` | 44 | 18 | `crates/zed-kernel/src/eval.rs:370` | row L6.13 |
| `alloc::vec::Vec<T, A>::dedup` | 30 | 13 | `crates/zed-kernel/src/types.rs:2127` | row STD-seq |
| `alloc::vec::Vec<T, A>::dedup_by` | 3 | 3 | `crates/zedc-elab/src/elab.rs:168` | row STD-seq |
| `alloc::vec::Vec<T, A>::drain` | 19 | 12 | `crates/zed-kernel/src/num/fast.rs:791` | missing |
| `alloc::vec::Vec<T, A>::extend_from_slice` | 30 | 13 | `crates/zed-native/src/codegen.rs:367` | row L6.13 |
| `alloc::vec::Vec<T, A>::insert` | 5 | 3 | `crates/zed-kernel/src/types/bdd.rs:1764` | row STD-seq |
| `alloc::vec::Vec<T, A>::into_boxed_slice` | 3 | 2 | `crates/zed-kernel/src/num.rs:108` | row L6.13 |
| `alloc::vec::Vec<T, A>::is_empty` | 294 | 53 | `crates/zed-kernel/src/eval.rs:1796` | `xs.count == 0` |
| `alloc::vec::Vec<T, A>::len` | 936 | 79 | `crates/zed-kernel/src/eval.rs:422` | `xs.count` |
| `alloc::vec::Vec<T, A>::pop` | 440 | 81 | `crates/zed-kernel/src/deep.rs:43` | row STD-seq |
| `alloc::vec::Vec<T, A>::pop_if` | 2 | 2 | `crates/zed-kernel/src/types.rs:973` | missing |
| `alloc::vec::Vec<T, A>::push` | 2051 | 103 | `crates/zed-kernel/src/eval.rs:84` | row L6.13 |
| `alloc::vec::Vec<T, A>::remove` | 11 | 9 | `crates/zed-kernel/src/eval.rs:935` | row STD-seq |
| `alloc::vec::Vec<T, A>::resize` | 9 | 7 | `crates/zed-kernel/src/num/fast.rs:341` | missing |
| `alloc::vec::Vec<T, A>::resize_with` | 5 | 4 | `crates/zed-kernel/src/types/print.rs:496` | missing |
| `alloc::vec::Vec<T, A>::retain` | 13 | 9 | `crates/zed-kernel/src/types.rs:334` | row STD-seq |
| `alloc::vec::Vec<T, A>::shrink_to` | 1 | 1 | `crates/zed-kernel/src/num/fast.rs:483` | missing |
| `alloc::vec::Vec<T, A>::shrink_to_fit` | 1 | 1 | `crates/zed-kernel/src/num/fast.rs:486` | missing |
| `alloc::vec::Vec<T, A>::splice` | 3 | 2 | `crates/zed-kernel/src/types/bdd.rs:1825` | missing |
| `alloc::vec::Vec<T, A>::split_off` | 16 | 11 | `crates/zed-kernel/src/term/walk.rs:106` | missing |
| `alloc::vec::Vec<T, A>::swap_remove` | 9 | 7 | `crates/zed-kernel/src/value.rs:870` | missing |
| `alloc::vec::Vec<T, A>::truncate` | 39 | 14 | `crates/zed-kernel/src/eval.rs:1732` | row L6.13 |
| `alloc::vec::Vec<T, A>::try_reserve` | 4 | 2 | `crates/zedc-zir/src/canon/serial.rs:42` | missing |
| `alloc::vec::Vec<T, A>::try_reserve_exact` | 3 | 3 | `crates/zed-kernel/src/num/room.rs:46` | row L6.13 |
| `alloc::vec::Vec<T>::new` | 884 | 95 | `crates/zed-kernel/src/deep.rs:20` | `[]` |
| `alloc::vec::Vec<T>::with_capacity` | 108 | 39 | `crates/zed-kernel/src/eval.rs:846` | row L6.13 |
| `alloc::vec::drain::<Drain<'_, T, A> as Iterator>::next` | 2 | 1 | `crates/zedc-zir/src/canon/binders.rs:668` | row STD-seq |
| `alloc::vec::into_iter::<IntoIter<T, A> as Iterator>::fold` | 7 | 4 | `crates/zed-kernel/src/provenance.rs:240` | `xs.foldl(z, f)` |
| `alloc::vec::into_iter::<IntoIter<T, A> as Iterator>::next` | 39 | 17 | `crates/zed-kernel/src/eval.rs:1029` | row STD-seq |
| `alloc::vec::partial_eq::<Vec<T, A1> as PartialEq<Vec<U, A2>>>::eq` | 42 | 8 | `crates/zed-kernel/src/types.rs:354` | `a == b` |
| `alloc::vec::partial_eq::<Vec<T, A1> as PartialEq<Vec<U, A2>>>::ne` | 18 | 3 | `crates/zedc-syntax/src/ast/node.rs:711` | `a != b` |
| `alloc::vec::partial_eq::<Vec<T, A> as PartialEq<&[U]>>::eq` | 6 | 1 | `crates/zedc-zir/src/zir/text.rs:598` | `a == b` |
| `blake3::<Hash as PartialEq<Self>>::eq` | 3 | 1 | `crates/zed-native/src/link.rs:314` | missing |
| `blake3::Hash::as_bytes` | 11 | 5 | `crates/zed-native/src/link.rs:313` | row STD-blake3 |
| `blake3::Hash::from_hex` | 1 | 1 | `crates/zed-native/src/link.rs:502` | missing |
| `blake3::Hash::to_hex` | 2 | 1 | `crates/zed-native/src/link.rs:230` | missing |
| `blake3::Hasher::finalize` | 9 | 5 | `crates/zed-native/src/link.rs:324` | row STD-blake3 |
| `blake3::Hasher::new` | 12 | 7 | `crates/zed-native/src/link.rs:320` | row STD-blake3 |
| `blake3::Hasher::new_derive_key` | 1 | 1 | `crates/zed-native/src/link.rs:738` | missing |
| `blake3::Hasher::update` | 50 | 7 | `crates/zed-native/src/link.rs:742` | row STD-blake3 |
| `blake3::Hasher::update_reader` | 2 | 1 | `crates/zed-native/src/link.rs:322` | missing |
| `core::any::TypeId::of` | 1 | 1 | `crates/zed-native/src/link.rs:838` | missing |
| `core::array::<[T; N] as Clone>::clone` | 19 | 2 | `crates/zed-kernel/src/text.rs:265` | `x` |
| `core::array::<[T; N] as Index<I>>::index` | 268 | 21 | `crates/zed-kernel/src/bits.rs:175` | `xs[i]` |
| `core::array::<[T; N] as IndexMut<I>>::index_mut` | 70 | 10 | `crates/zed-kernel/src/exact.rs:37` | row L6.13 |
| `core::array::<[T; N] as PartialOrd<Self>>::lt` | 12 | 1 | `crates/zedc-solvers/src/live3.rs:412` | `a < b` |
| `core::array::<[T; _] as Default>::default` | 1 | 1 | `crates/zedc-lattice/src/revision.rs:313` | missing |
| `core::array::[T; N]::as_slice` | 1 | 1 | `crates/zedc-presburger/src/presburger.rs:5317` | `x` |
| `core::array::[T; N]::each_ref` | 1 | 1 | `crates/zedc-solvers/src/live3.rs:879` | missing |
| `core::array::[T; N]::map` | 64 | 17 | `crates/zed-kernel/src/eval.rs:970` | missing |
| `core::array::equality::<[T; N] as PartialEq<[U; N]>>::eq` | 3 | 1 | `crates/zed-kernel/src/types/bdd.rs:551` | missing |
| `core::array::from_fn` | 2 | 1 | `crates/zed-kernel/src/text.rs:331` | missing |
| `core::array::iter::<[T; N] as IntoIterator>::into_iter` | 57 | 27 | `crates/zed-kernel/src/exact.rs:16` | row STD-seq |
| `core::bool::bool::then` | 69 | 26 | `crates/zed-kernel/src/num.rs:61` | missing |
| `core::bool::bool::then_some` | 57 | 22 | `crates/zed-kernel/src/num.rs:1665` | missing |
| `core::borrow::Borrow::borrow` | 5 | 2 | `crates/zedc-presburger/src/presburger.rs:3868` | `x` |
| `core::cell::<RefCell<T> as Default>::default` | 3 | 1 | `crates/zed-kernel/src/eval.rs:1672` | missing |
| `core::cell::<RefMut<'_, T> as DerefMut>::deref_mut` | 6 | 2 | `crates/zed-kernel/src/types/empty.rs:1702` | `x` |
| `core::cell::Cell<T>::get` | 5 | 4 | `crates/zed-kernel/src/value.rs:737` | missing |
| `core::cell::Cell<T>::new` | 17 | 8 | `crates/zed-kernel/src/deep.rs:19` | missing |
| `core::cell::Cell<T>::replace` | 2 | 2 | `crates/zed-kernel/src/deep.rs:31` | row L6.13 |
| `core::cell::Cell<T>::set` | 13 | 7 | `crates/zed-kernel/src/deep.rs:46` | missing |
| `core::cell::Cell<T>::take` | 3 | 1 | `crates/zed-kernel/src/frames.rs:85` | row L6.13 |
| `core::cell::RefCell<T>::borrow` | 17 | 3 | `crates/zed-kernel/src/eval.rs:1381` | `x` |
| `core::cell::RefCell<T>::borrow_mut` | 38 | 8 | `crates/zed-kernel/src/deep.rs:32` | `x` |
| `core::cell::RefCell<T>::into_inner` | 2 | 2 | `crates/zed-kernel/src/types.rs:1046` | `x` |
| `core::cell::RefCell<T>::new` | 21 | 10 | `crates/zed-kernel/src/deep.rs:20` | missing |
| `core::cell::RefCell<T>::take` | 2 | 1 | `crates/zed-kernel/src/eval.rs:1842` | row L6.13 |
| `core::cell::RefCell<T>::try_borrow_mut` | 3 | 2 | `crates/zed-kernel/src/types.rs:331` | missing |
| `core::cell::once::OnceCell<T>::get` | 4 | 1 | `crates/zedc-presburger/src/presburger.rs:3342` | missing |
| `core::cell::once::OnceCell<T>::get_or_init` | 5 | 3 | `crates/zedc-stage/src/stage.rs:120` | missing |
| `core::cell::once::OnceCell<T>::new` | 8 | 3 | `crates/zedc-presburger/src/presburger.rs:2659` | missing |
| `core::cell::once::OnceCell<T>::set` | 1 | 1 | `crates/zedc-presburger/src/presburger.rs:3366` | missing |
| `core::char::convert::<u32 as From<char>>::from` | 2 | 2 | `crates/zed-kernel/src/words.rs:129` | `int(x)` |
| `core::char::methods::char::encode_utf8` | 1 | 1 | `crates/zed-kernel/src/words.rs:133` | missing |
| `core::char::methods::char::from_u32` | 4 | 3 | `crates/zed-kernel/src/words.rs:132` | missing |
| `core::char::methods::char::is_alphabetic` | 1 | 1 | `crates/zedc-resolve/src/docs.rs:82` | missing |
| `core::char::methods::char::is_alphanumeric` | 3 | 3 | `crates/zedc-base/src/fence.rs:79` | missing |
| `core::char::methods::char::is_ascii_alphabetic` | 1 | 1 | `crates/zedc-syntax/src/parse/grammar.rs:397` | missing |
| `core::char::methods::char::is_ascii_alphanumeric` | 2 | 1 | `crates/zedc-syntax/src/parse/grammar.rs:135` | missing |
| `core::char::methods::char::is_ascii_digit` | 10 | 6 | `crates/zedc-base/src/fence.rs:77` | missing |
| `core::char::methods::char::is_digit` | 2 | 2 | `crates/zed-kernel/src/value.rs:468` | missing |
| `core::char::methods::char::is_whitespace` | 3 | 3 | `crates/zed-kernel/src/words.rs:205` | missing |
| `core::char::methods::char::len_utf8` | 10 | 4 | `crates/zed-kernel/src/words.rs:163` | `utf8(s).count` |
| `core::char::methods::char::to_lowercase` | 1 | 1 | `crates/zed-kernel/src/words.rs:186` | missing |
| `core::char::methods::char::to_uppercase` | 1 | 1 | `crates/zed-kernel/src/words.rs:162` | missing |
| `core::clone::Clone::clone` | 64 | 14 | `crates/zed-kernel/src/types/bdd.rs:240` | `x` |
| `core::clone::impls::<usize as Clone>::clone` | 1 | 1 | `crates/zedc-zir/src/canon/binders.rs:331` | `x` |
| `core::cmp::<Ordering as PartialEq<Self>>::eq` | 84 | 11 | `crates/zed-kernel/src/num.rs:715` | `a == b` |
| `core::cmp::Ord::clamp` | 1 | 1 | `crates/zed-kernel/src/num/bound.rs:351` | `min(max(x, a), b)` |
| `core::cmp::Ord::cmp` | 3 | 2 | `crates/zed-kernel/src/types/bdd/set.rs:124` | missing |
| `core::cmp::Ord::max` | 97 | 30 | `crates/zed-kernel/src/eval.rs:2253` | `max(a, b)` |
| `core::cmp::Ord::min` | 93 | 33 | `crates/zed-kernel/src/bits.rs:210` | `min(a, b)` |
| `core::cmp::Ordering::is_eq` | 2 | 2 | `crates/zed-kernel/src/types.rs:1683` | missing |
| `core::cmp::Ordering::is_gt` | 3 | 1 | `crates/zedc-solvers/src/live3.rs:383` | missing |
| `core::cmp::Ordering::is_le` | 1 | 1 | `crates/zed-kernel/src/types/bdd.rs:706` | missing |
| `core::cmp::Ordering::is_lt` | 1 | 1 | `crates/zed-kernel/src/types/bdd/set.rs:207` | missing |
| `core::cmp::Ordering::is_ne` | 6 | 2 | `crates/zed-kernel/src/types/rec.rs:966` | missing |
| `core::cmp::Ordering::reverse` | 8 | 3 | `crates/zed-kernel/src/num.rs:1430` | missing |
| `core::cmp::Ordering::then` | 11 | 5 | `crates/zed-kernel/src/provenance.rs:142` | missing |
| `core::cmp::Ordering::then_with` | 19 | 8 | `crates/zed-kernel/src/num/bound.rs:101` | missing |
| `core::cmp::PartialEq::eq` | 18 | 5 | `crates/zedc-lattice/src/cell.rs:210` | `a == b` |
| `core::cmp::PartialEq::ne` | 474 | 40 | `crates/zed-kernel/src/num.rs:1425` | `a != b` |
| `core::cmp::PartialOrd::ge` | 63 | 12 | `crates/zed-kernel/src/bits.rs:129` | `a >= b` |
| `core::cmp::PartialOrd::gt` | 102 | 16 | `crates/zed-kernel/src/num.rs:61` | `a > b` |
| `core::cmp::PartialOrd::le` | 93 | 13 | `crates/zed-kernel/src/num.rs:259` | `a <= b` |
| `core::cmp::PartialOrd::lt` | 138 | 13 | `crates/zed-kernel/src/bits.rs:154` | `a < b` |
| `core::cmp::impls::<&A as PartialEq<&B>>::eq` | 594 | 55 | `crates/zed-kernel/src/eval.rs:1535` | `a == b` |
| `core::cmp::impls::<&A as PartialEq<&B>>::ne` | 168 | 25 | `crates/zed-kernel/src/types/empty.rs:552` | `a != b` |
| `core::cmp::impls::<&A as PartialOrd<&B>>::ge` | 18 | 4 | `crates/zedc-int/src/int.rs:394` | `a >= b` |
| `core::cmp::impls::<&A as PartialOrd<&B>>::gt` | 23 | 5 | `crates/zedc-lattice/src/revision.rs:448` | `a > b` |
| `core::cmp::impls::<&A as PartialOrd<&B>>::le` | 30 | 5 | `crates/zedc-base/src/cost.rs:184` | `a <= b` |
| `core::cmp::impls::<&A as PartialOrd<&B>>::lt` | 31 | 6 | `crates/zed-kernel/src/num/fast.rs:603` | `a < b` |
| `core::cmp::impls::<&mut A as PartialEq<&B>>::eq` | 3 | 1 | `crates/zed-kernel/src/types/empty.rs:2503` | `a == b` |
| `core::cmp::impls::<bool as Ord>::cmp` | 16 | 4 | `crates/zed-kernel/src/num.rs:1439` | missing |
| `core::cmp::impls::<bool as PartialEq<Self>>::eq` | 180 | 15 | `crates/zed-kernel/src/eval.rs:2137` | `a == b` |
| `core::cmp::impls::<bool as PartialEq<Self>>::ne` | 72 | 12 | `crates/zed-kernel/src/types.rs:1237` | `a != b` |
| `core::cmp::impls::<char as PartialEq<Self>>::eq` | 78 | 9 | `crates/zedc-base/src/fence.rs:79` | `a == b` |
| `core::cmp::impls::<char as PartialEq<Self>>::ne` | 12 | 3 | `crates/zed-kernel/src/num.rs:1608` | `a != b` |
| `core::cmp::impls::<char as PartialOrd<Self>>::le` | 6 | 1 | `crates/zedc-syntax/src/parse/engine.rs:640` | `a <= b` |
| `core::cmp::impls::<f64 as PartialEq<Self>>::eq` | 21 | 5 | `crates/zed-kernel/src/eval.rs:2136` | `a == b` |
| `core::cmp::impls::<f64 as PartialOrd<Self>>::ge` | 3 | 1 | `crates/zed-kernel/src/eval.rs:2232` | `a >= b` |
| `core::cmp::impls::<f64 as PartialOrd<Self>>::gt` | 15 | 4 | `crates/zed-kernel/src/eval.rs:2231` | `a > b` |
| `core::cmp::impls::<f64 as PartialOrd<Self>>::le` | 3 | 1 | `crates/zed-kernel/src/eval.rs:2230` | `a <= b` |
| `core::cmp::impls::<f64 as PartialOrd<Self>>::lt` | 9 | 2 | `crates/zed-kernel/src/eval.rs:2139` | `a < b` |
| `core::cmp::impls::<f64 as PartialOrd<Self>>::partial_cmp` | 1 | 1 | `crates/zed-kernel/src/value.rs:1237` | missing |
| `core::cmp::impls::<i128 as Ord>::clamp` | 1 | 1 | `crates/zedc-preimage/src/preimage.rs:2493` | `min(max(x, a), b)` |
| `core::cmp::impls::<i128 as Ord>::cmp` | 1 | 1 | `crates/zedc-int/src/int.rs:258` | missing |
| `core::cmp::impls::<i128 as PartialEq<Self>>::eq` | 30 | 4 | `crates/zedc-check/src/check/widen.rs:724` | `a == b` |
| `core::cmp::impls::<i128 as PartialEq<Self>>::ne` | 15 | 3 | `crates/zed-kernel/src/num/fast.rs:1033` | `a != b` |
| `core::cmp::impls::<i128 as PartialOrd<Self>>::ge` | 9 | 1 | `crates/zedc-preimage/src/preimage.rs:6068` | `a >= b` |
| `core::cmp::impls::<i128 as PartialOrd<Self>>::gt` | 24 | 2 | `crates/zedc-int/src/int.rs:127` | `a > b` |
| `core::cmp::impls::<i128 as PartialOrd<Self>>::le` | 27 | 1 | `crates/zedc-preimage/src/preimage.rs:773` | `a <= b` |
| `core::cmp::impls::<i128 as PartialOrd<Self>>::lt` | 21 | 3 | `crates/zedc-check/src/check/widen.rs:792` | `a < b` |
| `core::cmp::impls::<i32 as PartialEq<Self>>::eq` | 24 | 6 | `crates/zed-kernel/src/types/bdd.rs:1293` | `a == b` |
| `core::cmp::impls::<i32 as PartialOrd<Self>>::ge` | 3 | 1 | `crates/zedc-lattice/src/float.rs:59` | `a >= b` |
| `core::cmp::impls::<i32 as PartialOrd<Self>>::gt` | 9 | 3 | `crates/zedc-lattice/src/iterate.rs:245` | `a > b` |
| `core::cmp::impls::<i32 as PartialOrd<Self>>::le` | 3 | 1 | `crates/zed-kernel/src/num.rs:1613` | `a <= b` |
| `core::cmp::impls::<i32 as PartialOrd<Self>>::lt` | 9 | 3 | `crates/zed-kernel/src/num.rs:1611` | `a < b` |
| `core::cmp::impls::<i64 as Ord>::cmp` | 2 | 2 | `crates/zed-kernel/src/value.rs:627` | missing |
| `core::cmp::impls::<i64 as PartialEq<Self>>::eq` | 78 | 8 | `crates/zed-kernel/src/bits.rs:199` | `a == b` |
| `core::cmp::impls::<i64 as PartialEq<Self>>::ne` | 21 | 4 | `crates/zed-kernel/src/eval.rs:2068` | `a != b` |
| `core::cmp::impls::<i64 as PartialOrd<Self>>::ge` | 21 | 5 | `crates/zed-kernel/src/num.rs:1581` | `a >= b` |
| `core::cmp::impls::<i64 as PartialOrd<Self>>::gt` | 27 | 4 | `crates/zed-kernel/src/bits.rs:183` | `a > b` |
| `core::cmp::impls::<i64 as PartialOrd<Self>>::le` | 33 | 2 | `crates/zed-kernel/src/bits.rs:202` | `a <= b` |
| `core::cmp::impls::<i64 as PartialOrd<Self>>::lt` | 21 | 3 | `crates/zed-kernel/src/bits.rs:175` | `a < b` |
| `core::cmp::impls::<i8 as Ord>::cmp` | 3 | 2 | `crates/zedc-int/src/int.rs:2470` | missing |
| `core::cmp::impls::<i8 as PartialEq<Self>>::eq` | 12 | 2 | `crates/zedc-int/src/int.rs:2230` | `a == b` |
| `core::cmp::impls::<i8 as PartialEq<Self>>::ne` | 6 | 1 | `crates/zedc-lattice/src/revision.rs:193` | `a != b` |
| `core::cmp::impls::<i8 as PartialOrd<Self>>::ge` | 21 | 2 | `crates/zedc-check/src/check/mod.rs:6301` | `a >= b` |
| `core::cmp::impls::<i8 as PartialOrd<Self>>::gt` | 15 | 2 | `crates/zedc-lattice/src/interval.rs:645` | `a > b` |
| `core::cmp::impls::<i8 as PartialOrd<Self>>::le` | 3 | 1 | `crates/zedc-preimage/src/preimage.rs:7073` | `a <= b` |
| `core::cmp::impls::<i8 as PartialOrd<Self>>::lt` | 36 | 4 | `crates/zedc-int/src/int.rs:1905` | `a < b` |
| `core::cmp::impls::<isize as PartialOrd<Self>>::gt` | 3 | 1 | `crates/zedc-presburger/src/presburger.rs:5980` | `a > b` |
| `core::cmp::impls::<isize as PartialOrd<Self>>::le` | 9 | 1 | `crates/zedc-presburger/src/presburger.rs:5352` | `a <= b` |
| `core::cmp::impls::<u128 as PartialEq<Self>>::eq` | 9 | 2 | `crates/zed-kernel/src/num.rs:1240` | `a == b` |
| `core::cmp::impls::<u128 as PartialEq<Self>>::ne` | 6 | 2 | `crates/zed-kernel/src/exact.rs:22` | `a != b` |
| `core::cmp::impls::<u128 as PartialOrd<Self>>::ge` | 3 | 1 | `crates/zed-kernel/src/num.rs:963` | `a >= b` |
| `core::cmp::impls::<u128 as PartialOrd<Self>>::gt` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:741` | missing |
| `core::cmp::impls::<u128 as PartialOrd<Self>>::le` | 18 | 3 | `crates/zed-kernel/src/num/fast.rs:430` | `a <= b` |
| `core::cmp::impls::<u128 as PartialOrd<Self>>::lt` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:397` | missing |
| `core::cmp::impls::<u16 as PartialEq<Self>>::ne` | 3 | 1 | `crates/zedc-check/src/check/mod.rs:4118` | missing |
| `core::cmp::impls::<u32 as Ord>::cmp` | 2 | 1 | `crates/zed-kernel/src/provenance.rs:138` | missing |
| `core::cmp::impls::<u32 as PartialEq<Self>>::eq` | 249 | 15 | `crates/zed-kernel/src/bits.rs:218` | `a == b` |
| `core::cmp::impls::<u32 as PartialEq<Self>>::ne` | 78 | 10 | `crates/zed-kernel/src/provenance.rs:100` | `a != b` |
| `core::cmp::impls::<u32 as PartialOrd<Self>>::ge` | 12 | 3 | `crates/zed-kernel/src/exact.rs:84` | `a >= b` |
| `core::cmp::impls::<u32 as PartialOrd<Self>>::gt` | 37 | 6 | `crates/zed-kernel/src/provenance.rs:125` | `a > b` |
| `core::cmp::impls::<u32 as PartialOrd<Self>>::le` | 9 | 2 | `crates/zedc-check/src/check/widen.rs:552` | `a <= b` |
| `core::cmp::impls::<u32 as PartialOrd<Self>>::lt` | 11 | 4 | `crates/zed-kernel/src/exact.rs:62` | `a < b` |
| `core::cmp::impls::<u64 as Ord>::cmp` | 18 | 4 | `crates/zed-kernel/src/num.rs:1005` | missing |
| `core::cmp::impls::<u64 as PartialEq<Self>>::eq` | 255 | 23 | `crates/zed-kernel/src/eval.rs:404` | `a == b` |
| `core::cmp::impls::<u64 as PartialEq<Self>>::ne` | 99 | 12 | `crates/zed-kernel/src/exact.rs:59` | `a != b` |
| `core::cmp::impls::<u64 as PartialOrd<Self>>::ge` | 60 | 7 | `crates/zed-kernel/src/num/bound.rs:125` | `a >= b` |
| `core::cmp::impls::<u64 as PartialOrd<Self>>::gt` | 81 | 8 | `crates/zed-kernel/src/num.rs:660` | `a > b` |
| `core::cmp::impls::<u64 as PartialOrd<Self>>::le` | 69 | 7 | `crates/zed-kernel/src/num/bound.rs:44` | `a <= b` |
| `core::cmp::impls::<u64 as PartialOrd<Self>>::lt` | 60 | 8 | `crates/zed-kernel/src/eval.rs:1382` | `a < b` |
| `core::cmp::impls::<u8 as Ord>::cmp` | 6 | 5 | `crates/zed-kernel/src/types/bdd.rs:1806` | missing |
| `core::cmp::impls::<u8 as PartialEq<Self>>::eq` | 177 | 14 | `crates/zed-kernel/src/types.rs:1111` | `a == b` |
| `core::cmp::impls::<u8 as PartialEq<Self>>::ne` | 105 | 9 | `crates/zed-kernel/src/types.rs:1063` | `a != b` |
| `core::cmp::impls::<u8 as PartialOrd<Self>>::ge` | 3 | 1 | `crates/zedc-syntax/src/format.rs:541` | `a >= b` |
| `core::cmp::impls::<u8 as PartialOrd<Self>>::le` | 3 | 1 | `crates/zedc-zir/src/zir/binary.rs:446` | `a <= b` |
| `core::cmp::impls::<u8 as PartialOrd<Self>>::lt` | 9 | 2 | `crates/zedc-check/src/check/mod.rs:1813` | `a < b` |
| `core::cmp::impls::<usize as Ord>::clamp` | 2 | 2 | `crates/zedc/src/front.rs:343` | `min(max(x, a), b)` |
| `core::cmp::impls::<usize as Ord>::cmp` | 6 | 4 | `crates/zed-kernel/src/types/bdd.rs:1920` | missing |
| `core::cmp::impls::<usize as PartialEq<Self>>::eq` | 1152 | 68 | `crates/zed-kernel/src/bits.rs:118` | `a == b` |
| `core::cmp::impls::<usize as PartialEq<Self>>::ne` | 354 | 40 | `crates/zed-kernel/src/bits.rs:170` | `a != b` |
| `core::cmp::impls::<usize as PartialOrd<Self>>::ge` | 159 | 31 | `crates/zed-kernel/src/eval.rs:1194` | `a >= b` |
| `core::cmp::impls::<usize as PartialOrd<Self>>::gt` | 492 | 48 | `crates/zed-kernel/src/eval.rs:452` | `a > b` |
| `core::cmp::impls::<usize as PartialOrd<Self>>::le` | 207 | 26 | `crates/zed-kernel/src/num.rs:1056` | `a <= b` |
| `core::cmp::impls::<usize as PartialOrd<Self>>::lt` | 401 | 48 | `crates/zed-kernel/src/num/fast.rs:309` | `a < b` |
| `core::convert::<T as Into<U>>::into` | 449 | 59 | `crates/zed-kernel/src/eval.rs:232` | `x` |
| `core::convert::<T as TryInto<U>>::try_into` | 7 | 3 | `crates/zedc-elab/src/elab/walk.rs:1397` | missing |
| `core::convert::AsRef::as_ref` | 1 | 1 | `crates/zedc/src/run.rs:767` | `x` |
| `core::convert::From::from` | 2 | 1 | `crates/zedc-presburger/src/presburger.rs:5513` | missing |
| `core::convert::Into::into` | 24 | 13 | `crates/zed-kernel/src/eval.rs:181` | `x` |
| `core::convert::num::<f64 as From<u8>>::from` | 2 | 1 | `crates/zed-kernel/src/types/empty.rs:909` | `f64(a)` |
| `core::convert::num::<i128 as From<bool>>::from` | 1 | 1 | `crates/zedc-check/src/check/widen.rs:827` | `if a { 1 } else { 0 }` |
| `core::convert::num::<i128 as From<i64>>::from` | 13 | 5 | `crates/zed-kernel/src/bits.rs:202` | `int(a)` |
| `core::convert::num::<i128 as From<u64>>::from` | 11 | 4 | `crates/zed-kernel/src/num/fast.rs:1046` | `int(a)` |
| `core::convert::num::<i128 as TryFrom<u128>>::try_from` | 3 | 2 | `crates/zedc-check/src/check/widen.rs:437` | missing |
| `core::convert::num::<i32 as From<bool>>::from` | 1 | 1 | `crates/zedc-int/src/int.rs:418` | `if a { 1 } else { 0 }` |
| `core::convert::num::<i32 as From<u8>>::from` | 1 | 1 | `crates/zed-native/src/exe.rs:171` | `int(a)` |
| `core::convert::num::<i64 as From<bool>>::from` | 5 | 3 | `crates/zed-native/src/hooks.rs:615` | `if a { 1 } else { 0 }` |
| `core::convert::num::<i64 as From<i32>>::from` | 1 | 1 | `crates/zedc-int/src/int.rs:1653` | `int(a)` |
| `core::convert::num::<i64 as From<u32>>::from` | 8 | 5 | `crates/zed-kernel/src/bits.rs:180` | `int(a)` |
| `core::convert::num::<i64 as From<u8>>::from` | 1 | 1 | `crates/zed-kernel/src/words.rs:242` | `int(a)` |
| `core::convert::num::<i64 as TryFrom<i128>>::try_from` | 16 | 5 | `crates/zed-kernel/src/bits.rs:204` | missing |
| `core::convert::num::<i64 as TryFrom<u64>>::try_from` | 1 | 1 | `crates/zedc-check/src/check/widen.rs:798` | missing |
| `core::convert::num::<u128 as From<u32>>::from` | 2 | 2 | `crates/zed-kernel/src/num/fast.rs:381` | `int(a)` |
| `core::convert::num::<u128 as From<u64>>::from` | 67 | 7 | `crates/zed-kernel/src/num.rs:959` | `int(a)` |
| `core::convert::num::<u32 as From<bool>>::from` | 6 | 3 | `crates/zed-kernel/src/num.rs:948` | `if a { 1 } else { 0 }` |
| `core::convert::num::<u32 as TryFrom<i64>>::try_from` | 8 | 6 | `crates/zed-kernel/src/eval.rs:2070` | missing |
| `core::convert::num::<u32 as TryFrom<u128>>::try_from` | 1 | 1 | `crates/zedc-check/src/check/widen.rs:706` | missing |
| `core::convert::num::<u32 as TryFrom<u64>>::try_from` | 2 | 2 | `crates/zed-kernel/src/num.rs:1232` | missing |
| `core::convert::num::<u64 as From<bool>>::from` | 21 | 9 | `crates/zed-kernel/src/num.rs:927` | `if a { 1 } else { 0 }` |
| `core::convert::num::<u64 as From<u32>>::from` | 7 | 6 | `crates/zed-kernel/src/num/fast.rs:1034` | `int(a)` |
| `core::convert::num::<u64 as From<u8>>::from` | 3 | 2 | `crates/zed-kernel/src/types.rs:121` | `int(a)` |
| `core::convert::num::<u64 as TryFrom<i128>>::try_from` | 3 | 3 | `crates/zed-kernel/src/types/empty.rs:1035` | missing |
| `core::convert::num::<u64 as TryFrom<u128>>::try_from` | 4 | 3 | `crates/zed-kernel/src/num.rs:964` | missing |
| `core::convert::num::<u8 as From<bool>>::from` | 14 | 6 | `crates/zed-kernel/src/types.rs:697` | `if a { 1 } else { 0 }` |
| `core::convert::num::<u8 as TryFrom<i64>>::try_from` | 1 | 1 | `crates/zed-kernel/src/words.rs:257` | missing |
| `core::convert::num::<usize as From<bool>>::from` | 31 | 18 | `crates/zed-kernel/src/types/bdd.rs:545` | `if a { 1 } else { 0 }` |
| `core::convert::num::ptr_try_from_impls::<i64 as TryFrom<usize>>::try_from` | 4 | 3 | `crates/zed-kernel/src/words.rs:120` | missing |
| `core::convert::num::ptr_try_from_impls::<u32 as TryFrom<usize>>::try_from` | 6 | 4 | `crates/zed-kernel/src/eval.rs:421` | missing |
| `core::convert::num::ptr_try_from_impls::<u64 as TryFrom<usize>>::try_from` | 1 | 1 | `crates/zed-kernel/src/num.rs:161` | missing |
| `core::convert::num::ptr_try_from_impls::<usize as TryFrom<i32>>::try_from` | 1 | 1 | `crates/zed-native/src/exe.rs:158` | missing |
| `core::convert::num::ptr_try_from_impls::<usize as TryFrom<i64>>::try_from` | 7 | 5 | `crates/zed-kernel/src/eval.rs:2279` | missing |
| `core::convert::num::ptr_try_from_impls::<usize as TryFrom<u128>>::try_from` | 1 | 1 | `crates/zed-kernel/src/words.rs:332` | missing |
| `core::convert::num::ptr_try_from_impls::<usize as TryFrom<u64>>::try_from` | 5 | 5 | `crates/zed-kernel/src/num/bound.rs:120` | missing |
| `core::default::Default::default` | 2 | 1 | `crates/zed-kernel/src/types/rec.rs:90` | missing |
| `core::f32::f32::from_bits` | 1 | 1 | `crates/zed-kernel/src/num.rs:948` | missing |
| `core::f64::f64::abs` | 3 | 2 | `crates/zed-kernel/src/words.rs:118` | `abs(a)` |
| `core::f64::f64::from_bits` | 5 | 4 | `crates/zed-kernel/src/exact.rs:65` | missing |
| `core::f64::f64::is_finite` | 2 | 1 | `crates/zedc-lattice/src/float.rs:64` | missing |
| `core::f64::f64::is_infinite` | 4 | 3 | `crates/zed-kernel/src/exact.rs:103` | missing |
| `core::f64::f64::is_nan` | 8 | 6 | `crates/zed-kernel/src/eval.rs:2132` | row STD-num |
| `core::f64::f64::is_sign_negative` | 3 | 3 | `crates/zed-kernel/src/eval.rs:2137` | missing |
| `core::f64::f64::to_bits` | 11 | 9 | `crates/zed-kernel/src/bits.rs:50` | `f64Bits(x)` |
| `core::f64::f64::total_cmp` | 2 | 2 | `crates/zed-kernel/src/types/empty.rs:944` | missing |
| `core::ffi::c_str::CStr::from_ptr` | 1 | 1 | `crates/zed-native/src/exe.rs:164` | missing |
| `core::ffi::c_str::CStr::to_bytes` | 1 | 1 | `crates/zed-native/src/exe.rs:164` | missing |
| `core::fmt::<Formatter<'_> as Write>::write_char` | 2 | 1 | `crates/zed-kernel/src/text.rs:679` | missing |
| `core::fmt::<[T] as Debug>::fmt` | 1 | 1 | `crates/zed-kernel/src/value.rs:182` | missing |
| `core::fmt::<str as Debug>::fmt` | 1 | 1 | `crates/zed-kernel/src/text.rs:658` | missing |
| `core::fmt::Formatter<'a>::align` | 1 | 1 | `crates/zed-kernel/src/text.rs:673` | missing |
| `core::fmt::Formatter<'a>::debug_list` | 1 | 1 | `crates/zedc-types/src/ty.rs:237` | missing |
| `core::fmt::Formatter<'a>::debug_struct` | 1 | 1 | `crates/zedc-types/src/ty.rs:302` | missing |
| `core::fmt::Formatter<'a>::fill` | 1 | 1 | `crates/zed-kernel/src/text.rs:678` | missing |
| `core::fmt::Formatter<'a>::precision` | 2 | 1 | `crates/zed-kernel/src/text.rs:666` | missing |
| `core::fmt::Formatter<'a>::width` | 2 | 1 | `crates/zed-kernel/src/text.rs:666` | missing |
| `core::fmt::Formatter<'a>::write_str` | 57 | 21 | `crates/zed-kernel/src/provenance.rs:163` | missing |
| `core::fmt::Write::write_str` | 6 | 2 | `crates/zed-kernel/src/print.rs:786` | missing |
| `core::fmt::builders::DebugList<'a, 'b>::entries` | 1 | 1 | `crates/zedc-types/src/ty.rs:237` | missing |
| `core::fmt::builders::DebugList<'a, 'b>::finish` | 1 | 1 | `crates/zedc-types/src/ty.rs:237` | missing |
| `core::fmt::builders::DebugStruct<'a, 'b>::field` | 2 | 1 | `crates/zedc-types/src/ty.rs:303` | missing |
| `core::fmt::builders::DebugStruct<'a, 'b>::finish` | 1 | 1 | `crates/zedc-types/src/ty.rs:305` | missing |
| `core::fmt::builders::from_fn` | 3 | 1 | `crates/zedc-check/src/check/mod.rs:333` | missing |
| `core::fmt::write` | 4 | 2 | `crates/zed-kernel/src/words.rs:317` | missing |
| `core::future::future::Future::poll` | 447 | 4 | `crates/zed-kernel/src/frames.rs:51` | missing |
| `core::hash::<BuildHasherDefault<H> as Default>::default` | 3 | 1 | `crates/zedc-types/src/ty.rs:105` | missing |
| `core::hash::BuildHasher::hash_one` | 3 | 1 | `crates/zedc-types/src/ty.rs:105` | missing |
| `core::hash::Hasher::write` | 3 | 1 | `crates/zed-kernel/src/text.rs:638` | missing |
| `core::hash::Hasher::write_u64` | 8 | 3 | `crates/zed-kernel/src/provenance.rs:154` | missing |
| `core::hash::Hasher::write_u8` | 2 | 2 | `crates/zed-kernel/src/text.rs:652` | missing |
| `core::hash::impls::<(T, B) as Hash>::hash` | 1 | 1 | `crates/zedc-resolve/src/resolve/tables.rs:48` | missing |
| `core::hash::impls::<*const T as Hash>::hash` | 1 | 1 | `crates/zedc-presburger/src/presburger/formula.rs:160` | missing |
| `core::hash::impls::<i128 as Hash>::hash` | 1 | 1 | `crates/zedc-int/src/int.rs:2588` | missing |
| `core::hash::impls::<i64 as Hash>::hash` | 1 | 1 | `crates/zedc-int/src/int.rs:2587` | missing |
| `core::hash::impls::<i8 as Hash>::hash` | 1 | 1 | `crates/zedc-int/src/int.rs:2589` | missing |
| `core::hash::impls::<u64 as Hash>::hash` | 1 | 1 | `crates/zed-kernel/src/types.rs:81` | missing |
| `core::hint::black_box` | 3 | 3 | `crates/zed-kernel/src/types/bdd.rs:2327` | row L6.13 |
| `core::intrinsics::transmute` | 1 | 1 | `crates/zed-native/src/lib.rs:160` | row L6.13 |
| `core::io::error::<ErrorKind as PartialEq<Self>>::eq` | 15 | 3 | `crates/zed-native/src/link.rs:564` | `a == b` |
| `core::io::error::Error::kind` | 5 | 3 | `crates/zed-native/src/link.rs:564` | missing |
| `core::io::util::sink` | 1 | 1 | `crates/zed-kernel/src/text.rs:1068` | missing |
| `core::io::write::Write::write_all` | 2 | 1 | `crates/zedc/src/run.rs:994` | missing |
| `core::iter::adapters::chain::<Chain<A, B> as Iterator>::count` | 6 | 2 | `crates/zed-kernel/src/types/rec.rs:174` | `xs.count` |
| `core::iter::adapters::chain::<Chain<A, B> as Iterator>::find` | 1 | 1 | `crates/zedc-zir/src/zir/validate.rs:262` | `xs.where(p).first` |
| `core::iter::adapters::chain::<Chain<A, B> as Iterator>::fold` | 1 | 1 | `crates/zed-kernel/src/types/rec.rs:201` | `xs.foldl(z, f)` |
| `core::iter::adapters::copied::<Copied<I> as Iterator>::next` | 1 | 1 | `crates/zedc-stage/src/stage.rs:363` | row STD-seq |
| `core::iter::adapters::filter::<Filter<I, P> as Clone>::clone` | 2 | 2 | `crates/zed-kernel/src/types.rs:2535` | `x` |
| `core::iter::adapters::filter::<Filter<I, P> as DoubleEndedIterator>::next_back` | 1 | 1 | `crates/zedc-zir/src/zir/memory.rs:676` | missing |
| `core::iter::adapters::filter::<Filter<I, P> as Iterator>::count` | 15 | 11 | `crates/zed-kernel/src/num/fast.rs:407` | `xs.count` |
| `core::iter::adapters::filter::<Filter<I, P> as Iterator>::fold` | 8 | 5 | `crates/zed-kernel/src/num.rs:1161` | `xs.foldl(z, f)` |
| `core::iter::adapters::filter::<Filter<I, P> as Iterator>::next` | 16 | 6 | `crates/zed-kernel/src/types/bdd.rs:1028` | row STD-seq |
| `core::iter::adapters::flatten::<FlatMap<I, U, F> as Iterator>::fold` | 2 | 2 | `crates/zedc-check/src/check/widen.rs:778` | `xs.foldl(z, f)` |
| `core::iter::adapters::flatten::<Flatten<I> as Iterator>::fold` | 2 | 2 | `crates/zedc-check/src/check/mod.rs:4117` | `xs.foldl(z, f)` |
| `core::iter::adapters::flatten::<Flatten<I> as Iterator>::next` | 4 | 2 | `crates/zedc-preimage/src/product.rs:1965` | row STD-seq |
| `core::iter::adapters::map::<Map<I, F> as Clone>::clone` | 1 | 1 | `crates/zed-kernel/src/types/empty.rs:3605` | `x` |
| `core::iter::adapters::map::<Map<I, F> as Iterator>::fold` | 8 | 5 | `crates/zed-kernel/src/text.rs:337` | `xs.foldl(z, f)` |
| `core::iter::adapters::map::<Map<I, F> as Iterator>::next` | 7 | 4 | `crates/zed-kernel/src/types.rs:963` | row STD-seq |
| `core::iter::adapters::peekable::<Peekable<I> as Iterator>::next` | 24 | 5 | `crates/zed-native/src/link.rs:394` | row STD-seq |
| `core::iter::adapters::peekable::Peekable<I>::next_if` | 6 | 4 | `crates/zedc-preimage/src/preimage.rs:5834` | missing |
| `core::iter::adapters::peekable::Peekable<I>::peek` | 13 | 6 | `crates/zed-native/src/link.rs:395` | `xs.first` |
| `core::iter::adapters::rev::<Rev<I> as ExactSizeIterator>::len` | 2 | 2 | `crates/zed-kernel/src/num.rs:1283` | `xs.count` |
| `core::iter::adapters::rev::<Rev<I> as Iterator>::find` | 1 | 1 | `crates/zed-kernel/src/exact.rs:59` | `xs.where(p).last` |
| `core::iter::adapters::rev::<Rev<I> as Iterator>::fold` | 20 | 12 | `crates/zed-kernel/src/num.rs:1239` | `xs.foldr((x, acc) -> f(acc, x), z)` |
| `core::iter::adapters::zip::<Zip<A, B> as Iterator>::fold` | 3 | 3 | `crates/zed-kernel/src/types/rec.rs:627` | `xs.foldl(z, f)` |
| `core::iter::sources::from_fn::from_fn` | 2 | 2 | `crates/zed-kernel/src/num.rs:1185` | missing |
| `core::iter::sources::once::once` | 19 | 10 | `crates/zed-kernel/src/num/fast.rs:715` | missing |
| `core::iter::sources::repeat::repeat` | 1 | 1 | `crates/zed-kernel/src/eval.rs:1316` | missing |
| `core::iter::sources::repeat_n::repeat_n` | 4 | 3 | `crates/zed-kernel/src/num/factor.rs:14` | missing |
| `core::iter::sources::successors::<Successors<T, F> as Iterator>::next` | 1 | 1 | `crates/zed-kernel/src/types/bdd/list.rs:253` | missing |
| `core::iter::sources::successors::successors` | 1 | 1 | `crates/zed-kernel/src/types/bdd/list.rs:154` | missing |
| `core::iter::traits::collect::<I as IntoIterator>::into_iter` | 1 | 1 | `crates/zedc-elab/src/elab.rs:449` | row STD-seq |
| `core::iter::traits::collect::IntoIterator::into_iter` | 23 | 10 | `crates/zed-kernel/src/types.rs:649` | row STD-seq |
| `core::iter::traits::exact_size::ExactSizeIterator::len` | 2 | 1 | `crates/zed-kernel/src/types/empty.rs:2303` | `xs.count` |
| `core::iter::traits::iterator::Iterator::all` | 80 | 27 | `crates/zed-kernel/src/eval.rs:2023` | `xs.all(p)` |
| `core::iter::traits::iterator::Iterator::any` | 75 | 24 | `crates/zed-kernel/src/exact.rs:52` | `xs.any(p)` |
| `core::iter::traits::iterator::Iterator::by_ref` | 8 | 5 | `crates/zed-kernel/src/num.rs:1292` | `x` |
| `core::iter::traits::iterator::Iterator::chain` | 108 | 38 | `crates/zed-kernel/src/eval.rs:1316` | `xs ++ ys` |
| `core::iter::traits::iterator::Iterator::cloned` | 138 | 23 | `crates/zed-kernel/src/eval.rs:440` | `x` |
| `core::iter::traits::iterator::Iterator::cmp` | 4 | 3 | `crates/zed-kernel/src/exact.rs:44` | missing |
| `core::iter::traits::iterator::Iterator::collect` | 1134 | 95 | `crates/zed-kernel/src/bits.rs:60` | `x` |
| `core::iter::traits::iterator::Iterator::copied` | 60 | 21 | `crates/zed-kernel/src/types.rs:1942` | `x` |
| `core::iter::traits::iterator::Iterator::count` | 9 | 9 | `crates/zed-kernel/src/text.rs:325` | `xs.count` |
| `core::iter::traits::iterator::Iterator::enumerate` | 268 | 55 | `crates/zed-kernel/src/bits.rs:117` | row STD-seq |
| `core::iter::traits::iterator::Iterator::eq` | 1 | 1 | `crates/zedc-presburger/src/conjuncts.rs:771` | missing |
| `core::iter::traits::iterator::Iterator::filter` | 277 | 46 | `crates/zed-kernel/src/eval.rs:1452` | `xs.where(p)` |
| `core::iter::traits::iterator::Iterator::filter_map` | 110 | 29 | `crates/zed-kernel/src/types.rs:352` | row STD-seq |
| `core::iter::traits::iterator::Iterator::find` | 41 | 24 | `crates/zed-kernel/src/types.rs:2383` | `xs.where(p).first` |
| `core::iter::traits::iterator::Iterator::find_map` | 9 | 6 | `crates/zed-kernel/src/types/empty.rs:2807` | row STD-seq |
| `core::iter::traits::iterator::Iterator::flat_map` | 86 | 27 | `crates/zed-kernel/src/num/fast.rs:524` | `xs.flatMap(f)` |
| `core::iter::traits::iterator::Iterator::flatten` | 86 | 25 | `crates/zed-kernel/src/eval.rs:815` | `xs.flatMap(x -> x)` |
| `core::iter::traits::iterator::Iterator::fold` | 10 | 6 | `crates/zed-kernel/src/types.rs:145` | `xs.foldl(z, f)` |
| `core::iter::traits::iterator::Iterator::for_each` | 24 | 10 | `crates/zed-kernel/src/provenance.rs:472` | missing |
| `core::iter::traits::iterator::Iterator::last` | 2 | 2 | `crates/zed-kernel/src/types/bdd/list.rs:288` | `xs.last` |
| `core::iter::traits::iterator::Iterator::map` | 1086 | 95 | `crates/zed-kernel/src/bits.rs:60` | `xs.map(f)` |
| `core::iter::traits::iterator::Iterator::map_while` | 1 | 1 | `crates/zed-native/src/link.rs:378` | missing |
| `core::iter::traits::iterator::Iterator::max` | 18 | 12 | `crates/zed-kernel/src/num/bound.rs:153` | `xs.maxBy(x -> x).last` |
| `core::iter::traits::iterator::Iterator::max_by_key` | 6 | 6 | `crates/zed-kernel/src/value.rs:413` | `xs.maxBy(f).last` |
| `core::iter::traits::iterator::Iterator::min` | 15 | 9 | `crates/zed-kernel/src/types/bes.rs:754` | `xs.minBy(x -> x).first` |
| `core::iter::traits::iterator::Iterator::min_by` | 1 | 1 | `crates/zed-kernel/src/types/empty.rs:944` | `xs.sort(by: f).first` |
| `core::iter::traits::iterator::Iterator::min_by_key` | 13 | 8 | `crates/zed-kernel/src/types.rs:2292` | `xs.minBy(f).first` |
| `core::iter::traits::iterator::Iterator::next` | 2 | 2 | `crates/zedc-types/src/ty.rs:1283` | row STD-seq |
| `core::iter::traits::iterator::Iterator::nth` | 4 | 4 | `crates/zed-kernel/src/provenance.rs:649` | `xs.drop(n).first` |
| `core::iter::traits::iterator::Iterator::partition` | 3 | 2 | `crates/zedc-preimage/src/product.rs:548` | missing |
| `core::iter::traits::iterator::Iterator::peekable` | 13 | 9 | `crates/zed-native/src/link.rs:393` | missing |
| `core::iter::traits::iterator::Iterator::position` | 5 | 3 | `crates/zed-native/src/link.rs:349` | `xs.find(p)` |
| `core::iter::traits::iterator::Iterator::product` | 4 | 4 | `crates/zed-kernel/src/types/empty.rs:933` | `xs.foldl(1, (a, b) -> a * b)` |
| `core::iter::traits::iterator::Iterator::reduce` | 6 | 5 | `crates/zedc-check/src/check/arms.rs:407` | `xs.reduce(f)` |
| `core::iter::traits::iterator::Iterator::rev` | 244 | 59 | `crates/zed-kernel/src/eval.rs:1989` | row STD-seq |
| `core::iter::traits::iterator::Iterator::skip` | 9 | 8 | `crates/zed-kernel/src/types/empty.rs:1517` | `xs.drop(n)` |
| `core::iter::traits::iterator::Iterator::step_by` | 7 | 4 | `crates/zed-kernel/src/num/fast.rs:282` | missing |
| `core::iter::traits::iterator::Iterator::sum` | 18 | 9 | `crates/zed-kernel/src/num.rs:659` | `sum(xs)` |
| `core::iter::traits::iterator::Iterator::take` | 5 | 3 | `crates/zed-kernel/src/num.rs:1292` | `xs.take(n)` |
| `core::iter::traits::iterator::Iterator::take_while` | 14 | 10 | `crates/zed-kernel/src/text.rs:325` | `xs.takeWhile(p)` |
| `core::iter::traits::iterator::Iterator::try_fold` | 4 | 3 | `crates/zedc-check/src/check/mod.rs:3192` | missing |
| `core::iter::traits::iterator::Iterator::try_for_each` | 11 | 7 | `crates/zed-kernel/src/provenance.rs:165` | missing |
| `core::iter::traits::iterator::Iterator::unzip` | 4 | 4 | `crates/zed-kernel/src/types.rs:856` | missing |
| `core::iter::traits::iterator::Iterator::zip` | 180 | 43 | `crates/zed-kernel/src/bits.rs:117` | `xs.take(ys.count).zip(ys.take(xs.count))` |
| `core::macros::assert_eq!` | 475 | 34 | `crates/zed-kernel/src/bits.rs:316` | row S.1d |
| `core::macros::assert_ne!` | 11 | 7 | `crates/zed-kernel/src/text.rs:876` | row S.1d |
| `core::macros::builtin::assert!` | 213 | 30 | `crates/zed-kernel/src/exact.rs:171` | row S.1d |
| `core::macros::builtin::cfg!` | 2 | 2 | `crates/zed-kernel/src/address.rs:12` | missing |
| `core::macros::builtin::concat!` | 2 | 1 | `crates/zed-native/src/link.rs:839` | missing |
| `core::macros::builtin::env!` | 6 | 3 | `crates/zed-native/src/link.rs:839` | missing |
| `core::macros::builtin::format_args!` | 11 | 3 | `crates/zed-kernel/src/words.rs:337` | missing |
| `core::macros::builtin::include!` | 2 | 1 | `crates/zed-native/src/link.rs:839` | missing |
| `core::macros::builtin::include_str!` | 2 | 1 | `crates/zedc-syntax/src/parse/mod.rs:37` | missing |
| `core::macros::builtin::line!` | 4 | 1 | `crates/zed-kernel/src/text.rs:1044` | missing |
| `core::macros::debug_assert!` | 27 | 14 | `crates/zed-kernel/src/num/fast.rs:510` | row S.1d |
| `core::macros::debug_assert_eq!` | 6 | 5 | `crates/zed-kernel/src/num/fast.rs:786` | row S.1d |
| `core::macros::matches!` | 279 | 59 | `crates/zed-kernel/src/bits.rs:29` | missing |
| `core::macros::todo!` | 4 | 1 | `crates/zed-kernel/src/text.rs:724` | row S.1d |
| `core::macros::unreachable!` | 215 | 52 | `crates/zed-kernel/src/eval.rs:398` | row S.1d |
| `core::macros::write!` | 183 | 35 | `crates/zed-kernel/src/num.rs:1537` | missing |
| `core::macros::writeln!` | 36 | 8 | `crates/zed-native/src/exe.rs:182` | missing |
| `core::mem::<Discriminant<T> as PartialEq<Self>>::eq` | 3 | 1 | `crates/zed-kernel/src/eval.rs:2240` | missing |
| `core::mem::discriminant` | 7 | 4 | `crates/zed-kernel/src/eval.rs:2240` | missing |
| `core::mem::drop` | 48 | 17 | `crates/zed-kernel/src/deep.rs:41` | row L6.13 |
| `core::mem::manually_drop::<ManuallyDrop<T> as DerefMut>::deref_mut` | 1 | 1 | `crates/zed-native/src/lib.rs:150` | `x` |
| `core::mem::manually_drop::ManuallyDrop<T>::into_inner` | 1 | 1 | `crates/zed-kernel/src/frames.rs:85` | `x` |
| `core::mem::manually_drop::ManuallyDrop<T>::new` | 3 | 2 | `crates/zed-kernel/src/frames.rs:37` | missing |
| `core::mem::manually_drop::ManuallyDrop<T>::take` | 1 | 1 | `crates/zed-native/src/lib.rs:100` | row L6.13 |
| `core::mem::replace` | 67 | 26 | `crates/zed-kernel/src/eval.rs:802` | row L6.13 |
| `core::mem::size_of` | 4 | 2 | `crates/zed-kernel/src/text.rs:1079` | row L6.13 |
| `core::mem::size_of_val` | 1 | 1 | `crates/zed-kernel/src/frames.rs:207` | row L6.13 |
| `core::mem::swap` | 6 | 2 | `crates/zedc-check/src/check/mod.rs:1849` | row L6.13 |
| `core::mem::take` | 157 | 38 | `crates/zed-kernel/src/eval.rs:348` | row L6.13 |
| `core::num::i128::abs` | 4 | 2 | `crates/zedc-preimage/src/preimage.rs:831` | `abs(a)` |
| `core::num::i128::checked_add` | 10 | 2 | `crates/zedc-int/src/int.rs:204` | missing |
| `core::num::i128::checked_mul` | 16 | 3 | `crates/zedc-int/src/int.rs:234` | missing |
| `core::num::i128::checked_neg` | 3 | 2 | `crates/zedc-int/src/int.rs:247` | missing |
| `core::num::i128::checked_pow` | 2 | 2 | `crates/zedc-check/src/check/widen.rs:830` | missing |
| `core::num::i128::checked_sub` | 5 | 2 | `crates/zedc-int/src/int.rs:217` | missing |
| `core::num::i128::checked_sub_unsigned` | 1 | 1 | `crates/zedc-int/src/int.rs:2008` | missing |
| `core::num::i128::div_euclid` | 4 | 3 | `crates/zedc-check/src/check/widen.rs:776` | `a div b` |
| `core::num::i128::rem_euclid` | 4 | 3 | `crates/zed-kernel/src/types/empty.rs:1035` | `a mod b` |
| `core::num::i128::trailing_zeros` | 1 | 1 | `crates/zed-kernel/src/num/fast.rs:1034` | missing |
| `core::num::i128::unsigned_abs` | 10 | 2 | `crates/zedc-int/src/int.rs:163` | `abs(a)` |
| `core::num::i64::checked_abs` | 1 | 1 | `crates/zed-kernel/src/words.rs:101` | missing |
| `core::num::i64::checked_add` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2065` | missing |
| `core::num::i64::checked_div_euclid` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2068` | missing |
| `core::num::i64::checked_mul` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2067` | missing |
| `core::num::i64::checked_neg` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2197` | missing |
| `core::num::i64::checked_pow` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2070` | missing |
| `core::num::i64::checked_rem_euclid` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2069` | missing |
| `core::num::i64::checked_sub` | 2 | 2 | `crates/zed-kernel/src/eval.rs:2066` | missing |
| `core::num::i64::count_ones` | 1 | 1 | `crates/zed-kernel/src/bits.rs:197` | `popCount(a)` |
| `core::num::i64::div_euclid` | 1 | 1 | `crates/zedc-int/src/int.rs:180` | `a div b` |
| `core::num::i64::leading_zeros` | 1 | 1 | `crates/zed-kernel/src/bits.rs:180` | `leadingZeros(a, width: 64)` |
| `core::num::i64::rem_euclid` | 5 | 2 | `crates/zedc-check/src/check/widen.rs:793` | `a mod b` |
| `core::num::i64::saturating_add` | 1 | 1 | `crates/zedc-check/src/check/widen.rs:811` | `min(max(a + b, -(2^63)), 2^63 - 1)` |
| `core::num::i64::signum` | 1 | 1 | `crates/zedc-int/src/int.rs:1872` | `if a > 0 { 1 } else if a < 0 { -1 } else { 0 }` |
| `core::num::i64::trailing_zeros` | 2 | 2 | `crates/zed-kernel/src/bits.rs:200` | `trailingZeros(a, width: 64)` |
| `core::num::i64::unsigned_abs` | 16 | 5 | `crates/zed-kernel/src/num/bound.rs:110` | `abs(a)` |
| `core::num::u128::checked_add` | 1 | 1 | `crates/zed-kernel/src/words.rs:357` | missing |
| `core::num::u128::checked_pow` | 1 | 1 | `crates/zedc-int/src/int.rs:2006` | missing |
| `core::num::u128::from_str_radix` | 1 | 1 | `crates/zedc-check/src/check/widen.rs:684` | row STD-num |
| `core::num::u128::is_power_of_two` | 1 | 1 | `crates/zedc-check/src/check/widen.rs:693` | `popCount(a) == 1` |
| `core::num::u128::saturating_add` | 2 | 1 | `crates/zedc-preimage/src/preimage.rs:5572` | `min(a + b, 2^128 - 1)` |
| `core::num::u128::saturating_mul` | 4 | 1 | `crates/zedc-preimage/src/preimage.rs:5572` | `min(a * b, 2^128 - 1)` |
| `core::num::u128::saturating_sub` | 3 | 1 | `crates/zed-kernel/src/words.rs:392` | `max(a - b, 0)` |
| `core::num::u128::trailing_zeros` | 2 | 2 | `crates/zed-kernel/src/num/fast.rs:381` | `trailingZeros(a, width: 128)` |
| `core::num::u128::wrapping_neg` | 1 | 1 | `crates/zed-kernel/src/num/fast.rs:1021` | missing |
| `core::num::u32::from_le_bytes` | 1 | 1 | `crates/zedc-zir/src/zir/binary.rs:395` | row STD-num |
| `core::num::u32::from_str_radix` | 3 | 2 | `crates/zedc-syntax/src/lex/string.rs:208` | row STD-num |
| `core::num::u32::ilog2` | 1 | 1 | `crates/zed-kernel/src/value.rs:480` | `31 - leadingZeros(a, width: 32)` |
| `core::num::u32::is_power_of_two` | 1 | 1 | `crates/zed-kernel/src/value.rs:480` | `popCount(a) == 1` |
| `core::num::u32::leading_zeros` | 3 | 2 | `crates/zedc-int/src/int.rs:2054` | `leadingZeros(a, width: 32)` |
| `core::num::u32::to_le_bytes` | 6 | 3 | `crates/zedc-zir/src/canon/mod.rs:180` | row STD-num |
| `core::num::u64::abs_diff` | 2 | 1 | `crates/zed-kernel/src/num/factor.rs:99` | `abs(a - b)` |
| `core::num::u64::checked_mul` | 1 | 1 | `crates/zed-kernel/src/types/empty.rs:830` | missing |
| `core::num::u64::div_ceil` | 6 | 3 | `crates/zed-kernel/src/num/fast.rs:849` | `-((-a) div b)` |
| `core::num::u64::from_le_bytes` | 2 | 2 | `crates/zed-native/src/exe.rs:82` | row STD-num |
| `core::num::u64::ilog2` | 3 | 2 | `crates/zed-kernel/src/num.rs:1224` | `63 - leadingZeros(a, width: 64)` |
| `core::num::u64::is_multiple_of` | 6 | 3 | `crates/zed-kernel/src/num/factor.rs:12` | `a mod b == 0` |
| `core::num::u64::is_power_of_two` | 2 | 2 | `crates/zed-kernel/src/num.rs:1224` | `popCount(a) == 1` |
| `core::num::u64::leading_zeros` | 7 | 5 | `crates/zed-kernel/src/exact.rs:61` | `leadingZeros(a, width: 64)` |
| `core::num::u64::next_multiple_of` | 1 | 1 | `crates/zed-kernel/src/num/fast.rs:1126` | missing |
| `core::num::u64::overflowing_add` | 7 | 1 | `crates/zed-kernel/src/num/fast.rs:452` | missing |
| `core::num::u64::overflowing_sub` | 5 | 2 | `crates/zed-kernel/src/exact.rs:35` | `((a - b) mod 2^64, a < b)` |
| `core::num::u64::rotate_left` | 3 | 3 | `crates/zed-kernel/src/provenance.rs:50` | `rotl(a, n, width: 64)` |
| `core::num::u64::saturating_add` | 9 | 1 | `crates/zedc-base/src/cost.rs:67` | `min(a + b, 2^64 - 1)` |
| `core::num::u64::saturating_mul` | 3 | 2 | `crates/zedc-base/src/cost.rs:67` | `min(a * b, 2^64 - 1)` |
| `core::num::u64::to_le_bytes` | 18 | 11 | `crates/zed-native/src/exe.rs:68` | row STD-num |
| `core::num::u64::trailing_zeros` | 3 | 2 | `crates/zed-kernel/src/num/factor.rs:13` | `trailingZeros(a, width: 64)` |
| `core::num::u64::wrapping_add` | 7 | 4 | `crates/zed-kernel/src/eval.rs:1980` | `(a + b) mod 2^64` |
| `core::num::u64::wrapping_mul` | 23 | 6 | `crates/zed-kernel/src/eval.rs:1982` | `(a * b) mod 2^64` |
| `core::num::u64::wrapping_neg` | 2 | 1 | `crates/zed-kernel/src/num/fast.rs:201` | missing |
| `core::num::u64::wrapping_sub` | 6 | 2 | `crates/zed-kernel/src/num/fast.rs:195` | `(a - b) mod 2^64` |
| `core::num::u8::count_ones` | 4 | 1 | `crates/zedc-check/src/check/mod.rs:2392` | `popCount(a)` |
| `core::num::u8::is_ascii_digit` | 12 | 8 | `crates/zed-kernel/src/num.rs:124` | missing |
| `core::num::u8::is_ascii_hexdigit` | 1 | 1 | `crates/zedc-syntax/src/lex/string.rs:204` | missing |
| `core::num::u8::is_ascii_whitespace` | 2 | 2 | `crates/zed-native/src/sources.rs:202` | missing |
| `core::num::usize::checked_add` | 1 | 1 | `crates/zed-kernel/src/text.rs:136` | missing |
| `core::num::usize::checked_mul` | 1 | 1 | `crates/zedc-zir/src/zir/binary.rs:603` | missing |
| `core::num::usize::checked_sub` | 14 | 8 | `crates/zed-kernel/src/print.rs:795` | missing |
| `core::num::usize::div_ceil` | 5 | 3 | `crates/zed-kernel/src/num/fast.rs:396` | `-((-a) div b)` |
| `core::num::usize::ilog2` | 1 | 1 | `crates/zed-kernel/src/num.rs:1068` | `63 - leadingZeros(a, width: 64)` |
| `core::num::usize::isolate_lowest_one` | 2 | 1 | `crates/zedc-preimage/src/preimage.rs:756` | row STD-num |
| `core::num::usize::next_power_of_two` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:380` | missing |
| `core::num::usize::saturating_add` | 1 | 1 | `crates/zedc-presburger/src/conjuncts.rs:1662` | `min(a + b, 2^64 - 1)` |
| `core::num::usize::saturating_sub` | 8 | 7 | `crates/zed-kernel/src/print.rs:871` | `max(a - b, 0)` |
| `core::num::usize::to_le_bytes` | 2 | 1 | `crates/zed-native/src/link.rs:742` | missing |
| `core::num::usize::trailing_zeros` | 2 | 2 | `crates/zed-kernel/src/exact.rs:195` | `trailingZeros(a, width: 64)` |
| `core::num::usize::wrapping_sub` | 1 | 1 | `crates/zedc-zir/src/canon/binders.rs:416` | `(a - b) mod 2^64` |
| `core::ops::arith::<&u32 as Add<u32>>::add` | 3 | 1 | `crates/zedc-presburger/src/presburger.rs:7434` | `a + b` |
| `core::ops::arith::<&u64 as Mul<Self>>::mul` | 3 | 1 | `crates/zedc-int/src/int.rs:1629` | `a * b` |
| `core::ops::arith::<&usize as Add<usize>>::add` | 10 | 4 | `crates/zed-kernel/src/text.rs:256` | `a + b` |
| `core::ops::arith::<f64 as Add<Self>>::add` | 6 | 2 | `crates/zed-kernel/src/eval.rs:2216` | `a + b` |
| `core::ops::arith::<f64 as Div<Self>>::div` | 6 | 2 | `crates/zed-kernel/src/eval.rs:2219` | `a / b` |
| `core::ops::arith::<f64 as Mul<Self>>::mul` | 6 | 2 | `crates/zed-kernel/src/eval.rs:2218` | `a * b` |
| `core::ops::arith::<f64 as Neg>::neg` | 3 | 2 | `crates/zed-kernel/src/eval.rs:2220` | `-a` |
| `core::ops::arith::<f64 as Sub<Self>>::sub` | 6 | 2 | `crates/zed-kernel/src/eval.rs:2217` | `a - b` |
| `core::ops::arith::<i128 as Add<Self>>::add` | 31 | 5 | `crates/zed-kernel/src/num/fast.rs:1049` | `a + b` |
| `core::ops::arith::<i128 as Div<Self>>::div` | 3 | 1 | `crates/zed-kernel/src/types/empty.rs:1030` | `if (a < 0) != (b < 0) { -(abs(a) div abs(b)) } else { abs(a) div abs(b) }` |
| `core::ops::arith::<i128 as Mul<Self>>::mul` | 36 | 5 | `crates/zed-kernel/src/num/fast.rs:1049` | `a * b` |
| `core::ops::arith::<i128 as Neg>::neg` | 20 | 4 | `crates/zedc-check/src/check/widen.rs:438` | `-a` |
| `core::ops::arith::<i128 as Rem<Self>>::rem` | 6 | 1 | `crates/zedc-preimage/src/preimage_ref.rs:3114` | `if a < 0 { -((-a) mod abs(b)) } else { a mod abs(b) }` |
| `core::ops::arith::<i128 as Sub<Self>>::sub` | 57 | 7 | `crates/zed-kernel/src/bits.rs:202` | `a - b` |
| `core::ops::arith::<i32 as Add<Self>>::add` | 13 | 2 | `crates/zed-kernel/src/num.rs:1613` | `a + b` |
| `core::ops::arith::<i32 as AddAssign<Self>>::add_assign` | 51 | 8 | `crates/zed-kernel/src/num/fast.rs:196` | `a + b` |
| `core::ops::arith::<i32 as Neg>::neg` | 25 | 9 | `crates/zed-kernel/src/num.rs:792` | `-a` |
| `core::ops::arith::<i32 as Sub<Self>>::sub` | 5 | 2 | `crates/zed-kernel/src/num.rs:1612` | `a - b` |
| `core::ops::arith::<i32 as SubAssign<Self>>::sub_assign` | 6 | 2 | `crates/zed-kernel/src/types/bdd.rs:1298` | `a - b` |
| `core::ops::arith::<i64 as Add<Self>>::add` | 18 | 4 | `crates/zed-kernel/src/num.rs:925` | `a + b` |
| `core::ops::arith::<i64 as AddAssign<Self>>::add_assign` | 15 | 3 | `crates/zed-kernel/src/eval.rs:1269` | `a + b` |
| `core::ops::arith::<i64 as Neg>::neg` | 24 | 12 | `crates/zed-kernel/src/eval.rs:2093` | `-a` |
| `core::ops::arith::<i64 as Rem<Self>>::rem` | 9 | 2 | `crates/zed-kernel/src/bits.rs:215` | `if a < 0 { -((-a) mod abs(b)) } else { a mod abs(b) }` |
| `core::ops::arith::<i64 as Sub<Self>>::sub` | 24 | 7 | `crates/zed-kernel/src/bits.rs:198` | `a - b` |
| `core::ops::arith::<i64 as SubAssign<Self>>::sub_assign` | 3 | 1 | `crates/zed-kernel/src/num/bound.rs:361` | `a - b` |
| `core::ops::arith::<i8 as Mul<Self>>::mul` | 9 | 1 | `crates/zedc-lattice/src/revision.rs:171` | `a * b` |
| `core::ops::arith::<i8 as Neg>::neg` | 3 | 2 | `crates/zedc-int/src/int.rs:1874` | `-a` |
| `core::ops::arith::<isize as Mul<Self>>::mul` | 3 | 1 | `crates/zedc-presburger/src/presburger.rs:5050` | `a * b` |
| `core::ops::arith::<isize as Sub<Self>>::sub` | 6 | 1 | `crates/zedc-presburger/src/presburger.rs:5049` | `a - b` |
| `core::ops::arith::<u128 as Add<Self>>::add` | 85 | 6 | `crates/zed-kernel/src/exact.rs:17` | `a + b` |
| `core::ops::arith::<u128 as AddAssign<Self>>::add_assign` | 9 | 2 | `crates/zed-kernel/src/num/fast.rs:743` | `a + b` |
| `core::ops::arith::<u128 as Div<Self>>::div` | 6 | 1 | `crates/zed-kernel/src/num/fast.rs:257` | missing |
| `core::ops::arith::<u128 as Mul<Self>>::mul` | 111 | 8 | `crates/zed-kernel/src/num.rs:959` | `a * b` |
| `core::ops::arith::<u128 as Rem<Self>>::rem` | 42 | 6 | `crates/zed-kernel/src/num.rs:1239` | `a mod b` |
| `core::ops::arith::<u128 as Sub<Self>>::sub` | 9 | 3 | `crates/zed-kernel/src/num.rs:963` | `a - b` |
| `core::ops::arith::<u128 as SubAssign<Self>>::sub_assign` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:742` | missing |
| `core::ops::arith::<u32 as Add<Self>>::add` | 78 | 9 | `crates/zed-kernel/src/exact.rs:61` | `a + b` |
| `core::ops::arith::<u32 as AddAssign<Self>>::add_assign` | 63 | 9 | `crates/zed-kernel/src/exact.rs:81` | `a + b` |
| `core::ops::arith::<u32 as Div<Self>>::div` | 6 | 1 | `crates/zed-kernel/src/exact.rs:12` | `a div b` |
| `core::ops::arith::<u32 as Mul<Self>>::mul` | 3 | 1 | `crates/zed-kernel/src/exact.rs:61` | `a * b` |
| `core::ops::arith::<u32 as Rem<Self>>::rem` | 9 | 2 | `crates/zed-kernel/src/exact.rs:13` | `a mod b` |
| `core::ops::arith::<u32 as Sub<Self>>::sub` | 66 | 10 | `crates/zed-kernel/src/bits.rs:180` | `a - b` |
| `core::ops::arith::<u32 as SubAssign<Self>>::sub_assign` | 27 | 2 | `crates/zed-kernel/src/types/bes.rs:421` | `a - b` |
| `core::ops::arith::<u64 as Add<&u64>>::add` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:1143` | missing |
| `core::ops::arith::<u64 as Add<Self>>::add` | 217 | 18 | `crates/zed-kernel/src/eval.rs:1990` | `a + b` |
| `core::ops::arith::<u64 as AddAssign<Self>>::add_assign` | 138 | 20 | `crates/zed-kernel/src/eval.rs:1657` | `a + b` |
| `core::ops::arith::<u64 as Div<Self>>::div` | 33 | 5 | `crates/zed-kernel/src/num/factor.rs:21` | `a div b` |
| `core::ops::arith::<u64 as DivAssign<Self>>::div_assign` | 3 | 1 | `crates/zed-kernel/src/types/empty.rs:752` | `a div b` |
| `core::ops::arith::<u64 as Mul<Self>>::mul` | 108 | 5 | `crates/zed-kernel/src/num/fast.rs:276` | `a * b` |
| `core::ops::arith::<u64 as MulAssign<Self>>::mul_assign` | 30 | 4 | `crates/zed-kernel/src/num/bound.rs:218` | `a * b` |
| `core::ops::arith::<u64 as Rem<Self>>::rem` | 111 | 7 | `crates/zed-kernel/src/eval.rs:1990` | `a mod b` |
| `core::ops::arith::<u64 as RemAssign<Self>>::rem_assign` | 3 | 1 | `crates/zed-kernel/src/num/factor.rs:41` | `a mod b` |
| `core::ops::arith::<u64 as Sub<&u64>>::sub` | 6 | 1 | `crates/zed-kernel/src/num/fast.rs:320` | missing |
| `core::ops::arith::<u64 as Sub<Self>>::sub` | 198 | 15 | `crates/zed-kernel/src/bits.rs:218` | `a - b` |
| `core::ops::arith::<u64 as SubAssign<Self>>::sub_assign` | 12 | 3 | `crates/zed-kernel/src/eval.rs:407` | `a - b` |
| `core::ops::arith::<u8 as Add<Self>>::add` | 21 | 3 | `crates/zed-kernel/src/types/empty.rs:3300` | `a + b` |
| `core::ops::arith::<u8 as AddAssign<Self>>::add_assign` | 3 | 1 | `crates/zedc-check/src/check/mod.rs:1818` | `a + b` |
| `core::ops::arith::<u8 as Sub<Self>>::sub` | 9 | 2 | `crates/zedc-base/src/address.rs:20` | `a - b` |
| `core::ops::arith::<usize as Add<&usize>>::add` | 12 | 4 | `crates/zed-kernel/src/text.rs:288` | `a + b` |
| `core::ops::arith::<usize as Add<Self>>::add` | 1528 | 76 | `crates/zed-kernel/src/eval.rs:1128` | `a + b` |
| `core::ops::arith::<usize as AddAssign<Self>>::add_assign` | 828 | 63 | `crates/zed-kernel/src/eval.rs:902` | `a + b` |
| `core::ops::arith::<usize as Div<Self>>::div` | 76 | 13 | `crates/zed-kernel/src/exact.rs:196` | `a div b` |
| `core::ops::arith::<usize as DivAssign<Self>>::div_assign` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:290` | missing |
| `core::ops::arith::<usize as Mul<&usize>>::mul` | 12 | 2 | `crates/zed-kernel/src/types/empty.rs:2373` | `a * b` |
| `core::ops::arith::<usize as Mul<Self>>::mul` | 239 | 20 | `crates/zed-kernel/src/num.rs:1288` | `a * b` |
| `core::ops::arith::<usize as MulAssign<Self>>::mul_assign` | 9 | 2 | `crates/zed-kernel/src/num/fast.rs:324` | `a * b` |
| `core::ops::arith::<usize as Rem<Self>>::rem` | 40 | 6 | `crates/zed-kernel/src/num.rs:1284` | `a mod b` |
| `core::ops::arith::<usize as Sub<Self>>::sub` | 698 | 62 | `crates/zed-kernel/src/bits.rs:182` | `a - b` |
| `core::ops::arith::<usize as SubAssign<Self>>::sub_assign` | 129 | 16 | `crates/zed-kernel/src/eval.rs:765` | `a - b` |
| `core::ops::arith::Add::add` | 18 | 2 | `crates/zedc-presburger/src/presburger.rs:5513` | `a + b` |
| `core::ops::arith::AddAssign::add_assign` | 12 | 1 | `crates/zed-kernel/src/print.rs:820` | `a + b` |
| `core::ops::arith::Mul::mul` | 12 | 2 | `crates/zed-kernel/src/num/fast.rs:127` | `a * b` |
| `core::ops::arith::Neg::neg` | 1 | 1 | `crates/zedc-base/src/axioms.rs:137` | `-a` |
| `core::ops::arith::Sub::sub` | 12 | 4 | `crates/zed-kernel/src/num.rs:955` | `a - b` |
| `core::ops::bit::<&bool as Not>::not` | 14 | 8 | `crates/zed-kernel/src/eval.rs:2258` | `!a` |
| `core::ops::bit::<&i128 as BitAnd<i128>>::bitand` | 3 | 1 | `crates/zedc-int/src/int.rs:140` | `bitAnd(a mod 2^128, b)` |
| `core::ops::bit::<&i64 as BitAnd<i64>>::bitand` | 3 | 1 | `crates/zedc-int/src/int.rs:1897` | `bitAnd(a mod 2^64, b)` |
| `core::ops::bit::<&u64 as Not>::not` | 1 | 1 | `crates/zed-kernel/src/num/fast.rs:320` | missing |
| `core::ops::bit::<&u64 as Shr<usize>>::shr` | 3 | 1 | `crates/zedc-zir/src/zir/legalize.rs:72` | `shr(a, n)` |
| `core::ops::bit::<bool as BitAndAssign<Self>>::bitand_assign` | 102 | 11 | `crates/zed-kernel/src/exact.rs:111` | `a && b` |
| `core::ops::bit::<bool as BitOr<Self>>::bitor` | 3 | 1 | `crates/zedc-presburger/src/presburger/deep.rs:480` | `a \|\| b` |
| `core::ops::bit::<bool as BitOrAssign<Self>>::bitor_assign` | 90 | 12 | `crates/zed-kernel/src/num/fast.rs:751` | `a \|\| b` |
| `core::ops::bit::<bool as Not>::not` | 1281 | 99 | `crates/zed-kernel/src/bits.rs:118` | `!a` |
| `core::ops::bit::<i128 as BitXor<Self>>::bitxor` | 3 | 1 | `crates/zedc-preimage/src/preimage.rs:6090` | `bitXor(a mod 2^128, b mod 2^128)` |
| `core::ops::bit::<i128 as Shl<i64>>::shl` | 6 | 1 | `crates/zed-kernel/src/bits.rs:202` | `shl(a, n)` |
| `core::ops::bit::<i128 as Shl<u32>>::shl` | 3 | 1 | `crates/zedc-check/src/check/widen.rs:550` | `shl(a, n)` |
| `core::ops::bit::<i128 as Shl<u64>>::shl` | 18 | 1 | `crates/zed-kernel/src/num/fast.rs:1026` | missing |
| `core::ops::bit::<i128 as Shr<i32>>::shr` | 6 | 1 | `crates/zedc-preimage/src/preimage.rs:6090` | `shr(a, n)` |
| `core::ops::bit::<i128 as Shr<u64>>::shr` | 6 | 1 | `crates/zed-kernel/src/num/fast.rs:1038` | missing |
| `core::ops::bit::<i64 as BitAnd<Self>>::bitand` | 3 | 1 | `crates/zed-kernel/src/bits.rs:194` | `bitAnd(a, b)` |
| `core::ops::bit::<i64 as BitOr<Self>>::bitor` | 3 | 1 | `crates/zed-kernel/src/bits.rs:195` | `bitOr(a, b)` |
| `core::ops::bit::<i64 as BitXor<Self>>::bitxor` | 3 | 1 | `crates/zed-kernel/src/bits.rs:196` | `bitXor(a, b)` |
| `core::ops::bit::<i64 as Shr<Self>>::shr` | 3 | 1 | `crates/zed-kernel/src/bits.rs:210` | `shr(a, n)` |
| `core::ops::bit::<u128 as BitAnd<Self>>::bitand` | 9 | 2 | `crates/zed-kernel/src/num.rs:962` | `bitAnd(a, b)` |
| `core::ops::bit::<u128 as BitOr<Self>>::bitor` | 18 | 2 | `crates/zed-kernel/src/num.rs:1239` | `bitOr(a, b)` |
| `core::ops::bit::<u128 as Shl<i32>>::shl` | 24 | 2 | `crates/zed-kernel/src/num.rs:1239` | `shl(a, n)` |
| `core::ops::bit::<u128 as Shl<u32>>::shl` | 3 | 1 | `crates/zed-kernel/src/exact.rs:14` | `shl(a, n)` |
| `core::ops::bit::<u128 as Shl<u64>>::shl` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:1024` | missing |
| `core::ops::bit::<u128 as Shr<i32>>::shr` | 45 | 3 | `crates/zed-kernel/src/exact.rs:16` | `shr(a, n)` |
| `core::ops::bit::<u128 as Shr<u32>>::shr` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:717` | missing |
| `core::ops::bit::<u128 as Shr<u64>>::shr` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:1025` | missing |
| `core::ops::bit::<u16 as BitAnd<Self>>::bitand` | 3 | 1 | `crates/zedc-check/src/check/mod.rs:4118` | missing |
| `core::ops::bit::<u16 as BitOr<Self>>::bitor` | 3 | 1 | `crates/zedc-check/src/check/mod.rs:4117` | missing |
| `core::ops::bit::<u16 as Shl<u8>>::shl` | 6 | 1 | `crates/zedc-check/src/check/mod.rs:4117` | missing |
| `core::ops::bit::<u32 as BitAnd<Self>>::bitand` | 42 | 3 | `crates/zed-kernel/src/num.rs:946` | `bitAnd(a, b)` |
| `core::ops::bit::<u32 as BitOr<Self>>::bitor` | 9 | 2 | `crates/zed-kernel/src/num.rs:946` | `bitOr(a, b)` |
| `core::ops::bit::<u32 as BitXor<Self>>::bitxor` | 6 | 1 | `crates/zedc-stage/src/stage.rs:614` | `bitXor(a, b)` |
| `core::ops::bit::<u32 as Not>::not` | 1 | 1 | `crates/zedc-stage/src/stage.rs:537` | `bitNot(a, width: 32)` |
| `core::ops::bit::<u32 as Shl<Self>>::shl` | 6 | 1 | `crates/zedc-stage/src/stage.rs:614` | `shl(a, n)` |
| `core::ops::bit::<u32 as Shl<i32>>::shl` | 9 | 1 | `crates/zed-kernel/src/num.rs:946` | `shl(a, n)` |
| `core::ops::bit::<u32 as Shr<Self>>::shr` | 3 | 1 | `crates/zedc-int/src/int.rs:2056` | `shr(a, n)` |
| `core::ops::bit::<u32 as Shr<i32>>::shr` | 3 | 1 | `crates/zed-kernel/src/num.rs:943` | `shr(a, n)` |
| `core::ops::bit::<u64 as BitAnd<Self>>::bitand` | 63 | 9 | `crates/zed-kernel/src/address.rs:17` | `bitAnd(a, b)` |
| `core::ops::bit::<u64 as BitOr<Self>>::bitor` | 21 | 4 | `crates/zed-kernel/src/bits.rs:221` | `bitOr(a, b)` |
| `core::ops::bit::<u64 as BitOrAssign<Self>>::bitor_assign` | 6 | 2 | `crates/zed-kernel/src/exact.rs:71` | `bitOr(a, b)` |
| `core::ops::bit::<u64 as BitXor<Self>>::bitxor` | 48 | 5 | `crates/zed-kernel/src/eval.rs:1982` | `bitXor(a, b)` |
| `core::ops::bit::<u64 as Shl<Self>>::shl` | 9 | 2 | `crates/zed-kernel/src/num/bound.rs:371` | `shl(a, n)` |
| `core::ops::bit::<u64 as Shl<i32>>::shl` | 39 | 4 | `crates/zed-kernel/src/exact.rs:79` | `shl(a, n)` |
| `core::ops::bit::<u64 as Shl<u32>>::shl` | 12 | 3 | `crates/zed-kernel/src/bits.rs:218` | `shl(a, n)` |
| `core::ops::bit::<u64 as Shl<usize>>::shl` | 15 | 3 | `crates/zed-kernel/src/num.rs:1128` | `shl(a, n)` |
| `core::ops::bit::<u64 as Shr<&usize>>::shr` | 3 | 1 | `crates/zed-kernel/src/num.rs:1160` | missing |
| `core::ops::bit::<u64 as Shr<i32>>::shr` | 51 | 7 | `crates/zed-kernel/src/eval.rs:1982` | `shr(a, n)` |
| `core::ops::bit::<u64 as Shr<u32>>::shr` | 15 | 4 | `crates/zed-kernel/src/bits.rs:220` | `shr(a, n)` |
| `core::ops::bit::<u64 as ShrAssign<i32>>::shr_assign` | 24 | 6 | `crates/zed-kernel/src/exact.rs:80` | `shr(a, n)` |
| `core::ops::bit::<u64 as ShrAssign<u32>>::shr_assign` | 3 | 1 | `crates/zedc-lattice/src/float.rs:57` | `shr(a, n)` |
| `core::ops::bit::<u8 as BitAnd<Self>>::bitand` | 150 | 6 | `crates/zed-kernel/src/types.rs:1063` | `bitAnd(a, b)` |
| `core::ops::bit::<u8 as BitAndAssign<Self>>::bitand_assign` | 9 | 2 | `crates/zedc-check/src/check/mod.rs:4140` | `bitAnd(a, b)` |
| `core::ops::bit::<u8 as BitOr<Self>>::bitor` | 42 | 5 | `crates/zed-kernel/src/types.rs:1086` | `bitOr(a, b)` |
| `core::ops::bit::<u8 as BitOrAssign<&u8>>::bitor_assign` | 3 | 1 | `crates/zedc-check/src/check/mod.rs:475` | `bitOr(a, b)` |
| `core::ops::bit::<u8 as BitOrAssign<Self>>::bitor_assign` | 24 | 2 | `crates/zedc-check/src/check/mod.rs:4177` | `bitOr(a, b)` |
| `core::ops::bit::<u8 as Not>::not` | 6 | 5 | `crates/zed-kernel/src/types.rs:1117` | `bitNot(a, width: 8)` |
| `core::ops::bit::<u8 as Shl<Self>>::shl` | 21 | 3 | `crates/zed-kernel/src/types.rs:697` | `shl(a, n)` |
| `core::ops::bit::<u8 as Shl<i32>>::shl` | 3 | 1 | `crates/zedc-base/src/address.rs:26` | `shl(a, n)` |
| `core::ops::bit::<u8 as Shl<usize>>::shl` | 3 | 1 | `crates/zedc-types/src/ty.rs:1167` | `shl(a, n)` |
| `core::ops::bit::<u8 as Shr<&u8>>::shr` | 3 | 1 | `crates/zed-kernel/src/types/empty.rs:3821` | `shr(a, n)` |
| `core::ops::bit::<usize as BitAnd<Self>>::bitand` | 9 | 2 | `crates/zedc-presburger/src/presburger/deep/canon.rs:333` | `bitAnd(a, b)` |
| `core::ops::bit::<usize as BitOr<Self>>::bitor` | 3 | 1 | `crates/zedc-syntax/src/parse/engine.rs:490` | `bitOr(a, b)` |
| `core::ops::bit::<usize as BitXor<Self>>::bitxor` | 48 | 3 | `crates/zed-kernel/src/types/empty.rs:3357` | `bitXor(a, b)` |
| `core::ops::bit::<usize as Not>::not` | 1 | 1 | `crates/zedc-syntax/src/parse/engine.rs:699` | `bitNot(a, width: 64)` |
| `core::ops::bit::<usize as Shl<Self>>::shl` | 6 | 2 | `crates/zed-kernel/src/num.rs:1076` | `shl(a, n)` |
| `core::ops::bit::<usize as Shl<u32>>::shl` | 3 | 1 | `crates/zed-kernel/src/exact.rs:195` | `shl(a, n)` |
| `core::ops::bit::<usize as Shr<Self>>::shr` | 3 | 1 | `crates/zedc-presburger/src/presburger/deep/canon.rs:333` | `shr(a, n)` |
| `core::ops::bit::Shl::shl` | 21 | 6 | `crates/zed-kernel/src/eval.rs:41` | `shl(a, n)` |
| `core::ops::deref::<&T as Deref>::deref` | 1427 | 97 | `crates/zed-kernel/src/bits.rs:166` | `x` |
| `core::ops::deref::<&mut T as Deref>::deref` | 425 | 59 | `crates/zed-kernel/src/bits.rs:166` | `x` |
| `core::ops::deref::Deref::deref` | 1 | 1 | `crates/zed-native/src/exe.rs:164` | `x` |
| `core::ops::index::Index::index` | 1850 | 85 | `crates/zed-kernel/src/bits.rs:129` | `xs[i]` |
| `core::ops::index::IndexMut::index_mut` | 124 | 27 | `crates/zed-kernel/src/address.rs:24` | row L6.13 |
| `core::ops::range::<Range<Idx> as Clone>::clone` | 3 | 2 | `crates/zed-kernel/src/types/empty.rs:2313` | `x` |
| `core::ops::range::Range<Idx>::contains` | 3 | 3 | `crates/zed-kernel/src/num.rs:1610` | `k in m` |
| `core::ops::range::RangeBounds::end_bound` | 1 | 1 | `crates/zedc-presburger/src/conjuncts.rs:80` | missing |
| `core::ops::range::RangeBounds::start_bound` | 1 | 1 | `crates/zedc-presburger/src/conjuncts.rs:75` | missing |
| `core::ops::range::RangeInclusive<Idx>::contains` | 3 | 2 | `crates/zed-kernel/src/text.rs:330` | `k in m` |
| `core::ops::try_trait::Try::branch` | 4 | 1 | `crates/zedc-presburger/src/presburger.rs:5513` | missing |
| `core::option::<Option<T> as Clone>::clone` | 78 | 20 | `crates/zed-kernel/src/eval.rs:841` | `x` |
| `core::option::<Option<T> as IntoIterator>::into_iter` | 27 | 16 | `crates/zed-kernel/src/types.rs:2256` | row STD-seq |
| `core::option::<Option<T> as Ord>::cmp` | 2 | 2 | `crates/zed-kernel/src/value.rs:643` | missing |
| `core::option::<Option<T> as PartialEq<Self>>::eq` | 288 | 34 | `crates/zed-kernel/src/eval.rs:2190` | `a == b` |
| `core::option::<Option<T> as Try>::branch` | 601 | 43 | `crates/zed-kernel/src/eval.rs:139` | missing |
| `core::option::Option<&T>::cloned` | 70 | 27 | `crates/zed-kernel/src/eval.rs:2261` | `x` |
| `core::option::Option<&T>::copied` | 67 | 29 | `crates/zed-kernel/src/eval.rs:413` | `x` |
| `core::option::Option<Option<T>>::flatten` | 24 | 16 | `crates/zed-kernel/src/eval.rs:413` | missing |
| `core::option::Option<Result<T, E>>::transpose` | 5 | 4 | `crates/zed-native/src/link.rs:866` | missing |
| `core::option::Option<T>::and_then` | 95 | 40 | `crates/zed-kernel/src/eval.rs:1418` | missing |
| `core::option::Option<T>::as_deref` | 28 | 12 | `crates/zed-kernel/src/types/bdd.rs:1973` | `x` |
| `core::option::Option<T>::as_deref_mut` | 2 | 2 | `crates/zedc-types/src/kernel_type.rs:34` | `x` |
| `core::option::Option<T>::as_mut` | 16 | 8 | `crates/zed-kernel/src/eval.rs:345` | `x` |
| `core::option::Option<T>::as_ref` | 217 | 38 | `crates/zed-kernel/src/eval.rs:139` | `x` |
| `core::option::Option<T>::expect` | 518 | 73 | `crates/zed-kernel/src/bits.rs:123` | row S.1d |
| `core::option::Option<T>::filter` | 68 | 24 | `crates/zed-kernel/src/num/fast.rs:848` | missing |
| `core::option::Option<T>::get_or_insert` | 15 | 8 | `crates/zed-kernel/src/types/empty.rs:1362` | missing |
| `core::option::Option<T>::get_or_insert_with` | 16 | 11 | `crates/zed-kernel/src/types.rs:2755` | missing |
| `core::option::Option<T>::is_none` | 143 | 43 | `crates/zed-kernel/src/eval.rs:2319` | missing |
| `core::option::Option<T>::is_none_or` | 46 | 17 | `crates/zed-kernel/src/types/bdd.rs:1549` | missing |
| `core::option::Option<T>::is_some` | 173 | 36 | `crates/zed-kernel/src/eval.rs:1803` | missing |
| `core::option::Option<T>::is_some_and` | 113 | 50 | `crates/zed-kernel/src/eval.rs:1194` | missing |
| `core::option::Option<T>::iter` | 7 | 5 | `crates/zedc-check/src/check/walk.rs:2161` | row STD-seq |
| `core::option::Option<T>::map` | 232 | 54 | `crates/zed-kernel/src/eval.rs:970` | missing |
| `core::option::Option<T>::map_or` | 87 | 39 | `crates/zed-kernel/src/num.rs:155` | missing |
| `core::option::Option<T>::map_or_else` | 18 | 9 | `crates/zed-kernel/src/types.rs:964` | missing |
| `core::option::Option<T>::ok_or` | 14 | 4 | `crates/zedc-presburger/src/presburger.rs:1816` | missing |
| `core::option::Option<T>::ok_or_else` | 42 | 15 | `crates/zed-kernel/src/value.rs:847` | missing |
| `core::option::Option<T>::or` | 10 | 5 | `crates/zed-kernel/src/types/empty.rs:196` | missing |
| `core::option::Option<T>::or_else` | 9 | 6 | `crates/zed-kernel/src/types/bdd.rs:607` | missing |
| `core::option::Option<T>::replace` | 7 | 6 | `crates/zed-kernel/src/types/empty.rs:1732` | missing |
| `core::option::Option<T>::take` | 92 | 31 | `crates/zed-kernel/src/deep.rs:32` | missing |
| `core::option::Option<T>::unwrap` | 5 | 3 | `crates/zedc-base/src/source.rs:186` | row S.1d |
| `core::option::Option<T>::unwrap_or` | 104 | 46 | `crates/zed-kernel/src/num.rs:123` | missing |
| `core::option::Option<T>::unwrap_or_default` | 27 | 17 | `crates/zed-kernel/src/eval.rs:133` | missing |
| `core::option::Option<T>::unwrap_or_else` | 51 | 21 | `crates/zed-kernel/src/eval.rs:1889` | missing |
| `core::option::Option<T>::zip` | 10 | 3 | `crates/zed-kernel/src/words.rs:357` | missing |
| `core::pin::Pin<&'a mut T>::get_mut` | 1 | 1 | `crates/zed-kernel/src/frames.rs:107` | row L6.13 |
| `core::pin::Pin<Ptr>::as_mut` | 1 | 1 | `crates/zed-kernel/src/frames.rs:82` | `x` |
| `core::ptr::const_ptr::*const T::add` | 1 | 1 | `crates/zed-native/src/exe.rs:164` | row S.4 |
| `core::ptr::const_ptr::*const T::cast` | 5 | 2 | `crates/zedc-presburger/src/presburger/formula.rs:144` | missing |
| `core::ptr::const_ptr::<*const T as PartialEq<Self>>::eq` | 3 | 1 | `crates/zedc-presburger/src/presburger/formula.rs:152` | `a == b` |
| `core::ptr::eq` | 10 | 10 | `crates/zed-kernel/src/num/fast.rs:476` | `a == b` |
| `core::ptr::null_mut` | 1 | 1 | `crates/zed-native/src/lib.rs:360` | missing |
| `core::result::<Result<T, E> as Clone>::clone` | 5 | 3 | `crates/zedc-presburger/src/presburger.rs:7033` | `x` |
| `core::result::<Result<T, E> as PartialEq<Self>>::eq` | 3 | 1 | `crates/zedc-check/src/check/mod.rs:6651` | `a == b` |
| `core::result::<Result<T, E> as Try>::branch` | 1079 | 64 | `crates/zed-kernel/src/bits.rs:57` | missing |
| `core::result::Result<T, E>::and_then` | 11 | 10 | `crates/zed-kernel/src/eval.rs:2103` | missing |
| `core::result::Result<T, E>::as_deref` | 1 | 1 | `crates/zedc/src/unit.rs:202` | `x` |
| `core::result::Result<T, E>::as_ref` | 1 | 1 | `crates/zedc-presburger/src/presburger.rs:7080` | `x` |
| `core::result::Result<T, E>::err` | 3 | 2 | `crates/zed-kernel/src/types/empty.rs:3354` | missing |
| `core::result::Result<T, E>::expect` | 72 | 29 | `crates/zed-kernel/src/eval.rs:421` | row S.1d |
| `core::result::Result<T, E>::is_err` | 15 | 8 | `crates/zed-kernel/src/eval.rs:1387` | missing |
| `core::result::Result<T, E>::is_ok` | 16 | 10 | `crates/zed-kernel/src/eval.rs:387` | missing |
| `core::result::Result<T, E>::is_ok_and` | 5 | 4 | `crates/zed-kernel/src/bits.rs:154` | missing |
| `core::result::Result<T, E>::map` | 40 | 17 | `crates/zed-kernel/src/bits.rs:232` | missing |
| `core::result::Result<T, E>::map_err` | 177 | 36 | `crates/zed-kernel/src/bits.rs:71` | missing |
| `core::result::Result<T, E>::map_or` | 1 | 1 | `crates/zedc-zir/src/zir/validate.rs:510` | missing |
| `core::result::Result<T, E>::map_or_else` | 4 | 4 | `crates/zed-kernel/src/types/print.rs:356` | missing |
| `core::result::Result<T, E>::ok` | 86 | 33 | `crates/zed-kernel/src/eval.rs:2070` | missing |
| `core::result::Result<T, E>::or_else` | 5 | 2 | `crates/zedc-presburger/src/presburger.rs:1165` | missing |
| `core::result::Result<T, E>::unwrap_or` | 2 | 2 | `crates/zed-native/src/exe.rs:158` | missing |
| `core::result::Result<T, E>::unwrap_or_else` | 9 | 7 | `crates/zed-native/src/hooks.rs:114` | missing |
| `core::slice::[T]::as_chunks` | 2 | 1 | `crates/zedc-syntax/src/ast/types.rs:42` | missing |
| `core::slice::[T]::binary_search` | 16 | 6 | `crates/zed-kernel/src/eval.rs:1387` | row STD-seq |
| `core::slice::[T]::binary_search_by` | 2 | 2 | `crates/zedc/src/run.rs:654` | row STD-seq |
| `core::slice::[T]::binary_search_by_key` | 3 | 2 | `crates/zed-kernel/src/num.rs:392` | row STD-seq |
| `core::slice::[T]::chunks` | 3 | 2 | `crates/zed-native/src/codegen.rs:185` | row STD-seq |
| `core::slice::[T]::chunks_exact_mut` | 2 | 1 | `crates/zed-kernel/src/num/fast.rs:280` | missing |
| `core::slice::[T]::clone_from_slice` | 1 | 1 | `crates/zedc-zir/src/canon/mod.rs:135` | missing |
| `core::slice::[T]::contains` | 30 | 16 | `crates/zed-kernel/src/types/bes.rs:117` | row STD-seq |
| `core::slice::[T]::copy_from_slice` | 1 | 1 | `crates/zed-kernel/src/text.rs:643` | missing |
| `core::slice::[T]::copy_within` | 1 | 1 | `crates/zed-kernel/src/num/fast.rs:733` | missing |
| `core::slice::[T]::ends_with` | 1 | 1 | `crates/zed-native/src/link.rs:884` | row STD-text |
| `core::slice::[T]::fill` | 5 | 4 | `crates/zed-kernel/src/address.rs:24` | missing |
| `core::slice::[T]::first` | 51 | 25 | `crates/zed-kernel/src/eval.rs:1442` | `xs.first` |
| `core::slice::[T]::first_mut` | 1 | 1 | `crates/zedc-int/src/int.rs:632` | row L6.13 |
| `core::slice::[T]::get` | 139 | 47 | `crates/zed-kernel/src/eval.rs:982` | `xs[i]` |
| `core::slice::[T]::get_mut` | 6 | 4 | `crates/zed-kernel/src/provenance.rs:656` | row L6.13 |
| `core::slice::[T]::is_empty` | 79 | 30 | `crates/zed-kernel/src/eval.rs:919` | `xs.count == 0` |
| `core::slice::[T]::iter` | 1701 | 106 | `crates/zed-kernel/src/bits.rs:60` | row STD-seq |
| `core::slice::[T]::iter_mut` | 56 | 19 | `crates/zed-kernel/src/bits.rs:164` | row L6.13 |
| `core::slice::[T]::last` | 69 | 37 | `crates/zed-kernel/src/bits.rs:123` | `xs.last` |
| `core::slice::[T]::last_mut` | 100 | 45 | `crates/zed-kernel/src/eval.rs:1498` | row L6.13 |
| `core::slice::[T]::len` | 298 | 62 | `crates/zed-kernel/src/bits.rs:170` | `xs.count` |
| `core::slice::[T]::partition_point` | 17 | 9 | `crates/zedc-base/src/source.rs:197` | row STD-seq |
| `core::slice::[T]::reverse` | 31 | 18 | `crates/zed-kernel/src/num.rs:1296` | row STD-seq |
| `core::slice::[T]::select_nth_unstable` | 1 | 1 | `crates/zedc-solvers/src/live3.rs:503` | missing |
| `core::slice::[T]::select_nth_unstable_by` | 1 | 1 | `crates/zedc-solvers/src/live3.rs:368` | missing |
| `core::slice::[T]::sort_unstable` | 45 | 21 | `crates/zed-kernel/src/num/factor.rs:24` | `xs.sort(asc x -> x)` |
| `core::slice::[T]::sort_unstable_by` | 5 | 4 | `crates/zedc-lattice/src/wto.rs:87` | `xs.sort(by: f)` |
| `core::slice::[T]::sort_unstable_by_key` | 6 | 5 | `crates/zed-kernel/src/num.rs:689` | `xs.sort(asc f)` |
| `core::slice::[T]::split` | 4 | 2 | `crates/zed-native/src/link.rs:377` | row STD-seq |
| `core::slice::[T]::split_at_checked` | 2 | 2 | `crates/zed-native/src/exe.rs:83` | missing |
| `core::slice::[T]::split_at_mut` | 6 | 4 | `crates/zed-kernel/src/num/fast.rs:281` | row L6.13 |
| `core::slice::[T]::split_first` | 32 | 10 | `crates/zed-kernel/src/eval.rs:916` | missing |
| `core::slice::[T]::split_first_chunk` | 2 | 1 | `crates/zed-native/src/exe.rs:79` | missing |
| `core::slice::[T]::split_last` | 17 | 8 | `crates/zed-kernel/src/value.rs:822` | missing |
| `core::slice::[T]::starts_with` | 4 | 3 | `crates/zed-native/src/link.rs:884` | row STD-text |
| `core::slice::[T]::strip_prefix` | 7 | 2 | `crates/zed-native/src/link.rs:386` | row STD-text |
| `core::slice::[T]::strip_suffix` | 3 | 2 | `crates/zed-native/src/link.rs:382` | row STD-text |
| `core::slice::[T]::swap` | 7 | 5 | `crates/zed-kernel/src/eval.rs:1990` | row L6.13 |
| `core::slice::[T]::windows` | 13 | 10 | `crates/zed-kernel/src/value.rs:393` | row STD-seq |
| `core::slice::cmp::<[T] as Ord>::cmp` | 2 | 2 | `crates/zed-kernel/src/text.rs:553` | missing |
| `core::slice::cmp::<[T] as PartialEq<[U]>>::eq` | 9 | 2 | `crates/zed-kernel/src/value.rs:159` | `a == b` |
| `core::slice::cmp::<[T] as PartialOrd<Self>>::le` | 3 | 1 | `crates/zedc-presburger/src/presburger.rs:5610` | `a <= b` |
| `core::slice::iter::<Iter<'a, T> as Iterator>::all` | 88 | 21 | `crates/zed-kernel/src/num.rs:203` | `xs.all(p)` |
| `core::slice::iter::<Iter<'a, T> as Iterator>::any` | 96 | 28 | `crates/zed-kernel/src/eval.rs:1450` | `xs.any(p)` |
| `core::slice::iter::<Iter<'a, T> as Iterator>::find` | 32 | 22 | `crates/zed-kernel/src/eval.rs:1892` | `xs.where(p).first` |
| `core::slice::iter::<Iter<'a, T> as Iterator>::find_map` | 10 | 5 | `crates/zedc-check/src/check/mod.rs:4964` | row STD-seq |
| `core::slice::iter::<Iter<'a, T> as Iterator>::fold` | 42 | 19 | `crates/zed-kernel/src/provenance.rs:398` | `xs.foldl(z, f)` |
| `core::slice::iter::<Iter<'a, T> as Iterator>::for_each` | 28 | 9 | `crates/zed-kernel/src/types/empty.rs:373` | missing |
| `core::slice::iter::<Iter<'a, T> as Iterator>::next` | 17 | 7 | `crates/zed-kernel/src/types.rs:1671` | row STD-seq |
| `core::slice::iter::<Iter<'a, T> as Iterator>::position` | 25 | 15 | `crates/zed-kernel/src/types/rec.rs:695` | row STD-seq |
| `core::slice::iter::<Iter<'a, T> as Iterator>::rposition` | 1 | 1 | `crates/zedc-resolve/src/resolve.rs:839` | row STD-seq |
| `core::slice::iter::<IterMut<'a, T> as Iterator>::find` | 1 | 1 | `crates/zedc-check/src/check/mod.rs:2150` | `xs.where(p).first` |
| `core::slice::iter::<IterMut<'a, T> as Iterator>::for_each` | 5 | 1 | `crates/zedc-zir/src/zir/canon.rs:91` | missing |
| `core::slice::iter::<IterMut<'a, T> as Iterator>::next` | 1 | 1 | `crates/zed-kernel/src/num/fast.rs:451` | missing |
| `core::slice::iter::<Split<'a, T, P> as Iterator>::next` | 3 | 1 | `crates/zed-native/src/link.rs:630` | missing |
| `core::slice::iter::Iter<'a, T>::as_slice` | 3 | 1 | `crates/zedc-presburger/src/presburger/deep/canon.rs:101` | `x` |
| `core::slice::raw::from_raw_parts` | 1 | 1 | `crates/zed-native/src/exe.rs:166` | missing |
| `core::slice::raw::from_ref` | 21 | 13 | `crates/zed-kernel/src/eval.rs:1470` | `[x]` |
| `core::str::converts::from_utf8` | 11 | 7 | `crates/zed-kernel/src/text.rs:999` | `fromUtf8(b)` |
| `core::str::error::Utf8Error::error_len` | 1 | 1 | `crates/zedc-base/src/source.rs:113` | missing |
| `core::str::error::Utf8Error::valid_up_to` | 1 | 1 | `crates/zedc-base/src/source.rs:112` | missing |
| `core::str::iter::<Bytes<'_> as Iterator>::all` | 7 | 4 | `crates/zed-kernel/src/num.rs:124` | `xs.all(p)` |
| `core::str::iter::<CharIndices<'a> as Iterator>::next` | 3 | 1 | `crates/zedc-zir/src/zir/text.rs:1236` | row STD-text |
| `core::str::iter::<Chars<'a> as Iterator>::count` | 5 | 4 | `crates/zed-kernel/src/text.rs:565` | `len(s)` |
| `core::str::iter::<Chars<'a> as Iterator>::next` | 17 | 10 | `crates/zed-kernel/src/words.rs:230` | row STD-text |
| `core::str::iter::<RSplit<'a, P> as Iterator>::next` | 2 | 1 | `crates/zedc-resolve/src/resolve.rs:946` | row STD-seq |
| `core::str::iter::<Split<'a, P> as Iterator>::next` | 2 | 2 | `crates/zedc-zir/src/zir/text.rs:715` | row STD-seq |
| `core::str::str::as_bytes` | 48 | 19 | `crates/zed-kernel/src/text.rs:541` | `utf8(s)` |
| `core::str::str::bytes` | 13 | 7 | `crates/zed-kernel/src/num.rs:124` | `utf8(s)` |
| `core::str::str::char_indices` | 10 | 9 | `crates/zed-kernel/src/text.rs:686` | row STD-text |
| `core::str::str::chars` | 33 | 19 | `crates/zed-kernel/src/num.rs:1608` | row STD-text |
| `core::str::str::contains` | 13 | 7 | `crates/zed-kernel/src/types/print.rs:458` | row STD-text |
| `core::str::str::ends_with` | 16 | 6 | `crates/zed-kernel/src/words.rs:61` | row STD-text |
| `core::str::str::find` | 14 | 9 | `crates/zed-kernel/src/num.rs:118` | missing |
| `core::str::str::is_empty` | 22 | 8 | `crates/zed-kernel/src/num.rs:125` | `len(s) == 0` |
| `core::str::str::len` | 79 | 27 | `crates/zed-kernel/src/num.rs:155` | `utf8(s).count` |
| `core::str::str::lines` | 5 | 4 | `crates/zed-native/src/sources.rs:48` | `lines(s)` |
| `core::str::str::match_indices` | 2 | 1 | `crates/zedc-syntax/src/lex/string.rs:52` | row STD-text |
| `core::str::str::matches` | 2 | 2 | `crates/zedc-syntax/src/format.rs:418` | missing |
| `core::str::str::parse` | 19 | 12 | `crates/zed-kernel/src/num.rs:1074` | missing |
| `core::str::str::rfind` | 1 | 1 | `crates/zedc-syntax/src/lex/string.rs:363` | row STD-text |
| `core::str::str::rsplit` | 2 | 1 | `crates/zedc-resolve/src/resolve.rs:946` | missing |
| `core::str::str::rsplit_once` | 2 | 2 | `crates/zed-native/src/sources.rs:257` | row STD-text |
| `core::str::str::split` | 11 | 9 | `crates/zed-native/src/sources.rs:289` | `s.split(t)` |
| `core::str::str::split_at` | 4 | 2 | `crates/zed-kernel/src/num.rs:1076` | missing |
| `core::str::str::split_once` | 17 | 8 | `crates/zed-kernel/src/num.rs:123` | row STD-text |
| `core::str::str::starts_with` | 44 | 16 | `crates/zed-kernel/src/words.rs:475` | row STD-text |
| `core::str::str::strip_prefix` | 24 | 14 | `crates/zed-kernel/src/num.rs:1018` | row STD-text |
| `core::str::str::strip_suffix` | 11 | 7 | `crates/zed-kernel/src/words.rs:468` | row STD-text |
| `core::str::str::trim` | 19 | 5 | `crates/zed-kernel/src/print.rs:134` | `trim(s)` |
| `core::str::str::trim_end` | 4 | 3 | `crates/zed-kernel/src/print.rs:843` | row STD-text |
| `core::str::str::trim_end_matches` | 3 | 2 | `crates/zed-native/src/sources.rs:253` | row STD-text |
| `core::str::str::trim_matches` | 3 | 2 | `crates/zedc-check/src/check/mod.rs:4070` | row STD-text |
| `core::str::str::trim_start` | 2 | 2 | `crates/zedc-base/src/fence.rs:62` | row STD-text |
| `core::str::str::trim_start_matches` | 5 | 3 | `crates/zedc-syntax/src/lex/string.rs:388` | row STD-text |
| `core::str::traits::<str as Ord>::cmp` | 3 | 3 | `crates/zedc-lattice/src/wto.rs:38` | missing |
| `core::str::traits::<str as PartialEq<Self>>::eq` | 6 | 1 | `crates/zedc-check/src/check/walk.rs:2020` | `a == b` |
| `core::sync::atomic::Atomic<bool>::load` | 1 | 1 | `crates/zed-kernel/src/types/bdd.rs:854` | missing |
| `core::sync::atomic::Atomic<bool>::new` | 1 | 1 | `crates/zed-kernel/src/types/bdd.rs:743` | missing |
| `core::sync::atomic::Atomic<bool>::store` | 1 | 1 | `crates/zed-kernel/src/types/bdd.rs:868` | missing |
| `core::sync::atomic::Atomic<u64>::fetch_add` | 9 | 8 | `crates/zed-kernel/src/types/bdd.rs:737` | missing |
| `core::sync::atomic::Atomic<u64>::new` | 6 | 6 | `crates/zed-kernel/src/types/bdd.rs:46` | missing |
| `core::task::wake::Context<'a>::from_waker` | 1 | 1 | `crates/zed-kernel/src/frames.rs:80` | missing |
| `core::task::wake::Waker::noop` | 1 | 1 | `crates/zed-kernel/src/frames.rs:80` | missing |
| `core::tuple::<(U, T) as Default>::default` | 1 | 1 | `crates/zed-kernel/src/eval.rs:1660` | missing |
| `core::tuple::<(U, T) as Ord>::cmp` | 5 | 5 | `crates/zed-kernel/src/types/bdd/set.rs:205` | missing |
| `core::tuple::<(U, T) as PartialEq<Self>>::eq` | 24 | 5 | `crates/zed-native/src/hooks.rs:363` | `a == b` |
| `core::tuple::<(U, T) as PartialEq<Self>>::ne` | 3 | 1 | `crates/zedc-presburger/src/presburger.rs:4677` | `a != b` |
| `core::tuple::<(U, T) as PartialOrd<Self>>::gt` | 3 | 1 | `crates/zed-kernel/src/types/bdd/set.rs:71` | missing |
| `core::tuple::<(U, T) as PartialOrd<Self>>::le` | 3 | 1 | `crates/zedc-lattice/src/interval.rs:227` | `a <= b` |
| `core::tuple::<(U, T) as PartialOrd<Self>>::lt` | 6 | 1 | `crates/zed-kernel/src/types/bdd/set.rs:147` | missing |
| `core::tuple::<(V, U, T) as Ord>::cmp` | 3 | 3 | `crates/zed-kernel/src/num.rs:1478` | missing |
| `core::tuple::<(V, U, T) as PartialEq<Self>>::eq` | 3 | 1 | `crates/zedc-elab/src/elab.rs:168` | `a == b` |
| `core::tuple::<(V, U, T) as PartialOrd<Self>>::lt` | 3 | 1 | `crates/zedc-presburger/src/presburger.rs:4499` | `a < b` |
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
| `cranelift_codegen::ir::builder::InstBuilder::symbol_value` | 1 | 1 | `crates/zed-native/src/exe.rs:129` | row S.4 |
| `cranelift_codegen::ir::builder::InstBuilder::uextend` | 1 | 1 | `crates/zed-native/src/codegen.rs:583` | row S.4 |
| `cranelift_codegen::ir::extfunc::AbiParam::new` | 6 | 2 | `crates/zed-native/src/codegen.rs:59` | row S.4 |
| `cranelift_codegen::ir::instructions::<BlockArg as From<Value>>::from` | 2 | 1 | `crates/zed-native/src/codegen.rs:53` | row S.4 |
| `cranelift_codegen::ir::memflags::MemFlagsData::new` | 2 | 1 | `crates/zed-native/src/codegen.rs:570` | row S.4 |
| `cranelift_codegen::ir::stackslot::StackSlotData::new` | 1 | 1 | `crates/zed-native/src/codegen.rs:323` | row S.4 |
| `cranelift_codegen::isa::IsaBuilder<T>::finish` | 1 | 1 | `crates/zed-native/src/lib.rs:82` | row S.4 |
| `cranelift_codegen::isa::TargetFrontendConfig::pointer_type` | 1 | 1 | `crates/zed-native/src/exe.rs:107` | row S.4 |
| `cranelift_codegen::isa::dyn TargetIsa + 'a::frontend_config` | 2 | 2 | `crates/zed-native/src/codegen.rs:195` | row S.4 |
| `cranelift_codegen::settings::<Builder as Configurable>::set` | 1 | 1 | `crates/zed-native/src/lib.rs:58` | row S.4 |
| `cranelift_codegen::settings::Flags::new` | 1 | 1 | `crates/zed-native/src/lib.rs:82` | row S.4 |
| `cranelift_codegen::settings::builder` | 1 | 1 | `crates/zed-native/src/lib.rs:57` | row S.4 |
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
| `cranelift_frontend::frontend::FunctionBuilder<'a>::seal_block` | 1 | 1 | `crates/zed-native/src/exe.rs:126` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilder<'a>::switch_to_block` | 20 | 2 | `crates/zed-native/src/codegen.rs:177` | row S.4 |
| `cranelift_frontend::frontend::FunctionBuilderContext::new` | 2 | 2 | `crates/zed-native/src/codegen.rs:172` | row S.4 |
| `cranelift_frontend::switch::Switch::emit` | 1 | 1 | `crates/zed-native/src/codegen.rs:761` | row S.4 |
| `cranelift_frontend::switch::Switch::new` | 1 | 1 | `crates/zed-native/src/codegen.rs:757` | row S.4 |
| `cranelift_frontend::switch::Switch::set_entry` | 1 | 1 | `crates/zed-native/src/codegen.rs:759` | row S.4 |
| `cranelift_jit::backend::JITBuilder::memory_provider` | 1 | 1 | `crates/zed-native/src/lib.rs:145` | row S.4 |
| `cranelift_jit::backend::JITBuilder::symbol` | 1 | 1 | `crates/zed-native/src/lib.rs:147` | row S.4 |
| `cranelift_jit::backend::JITBuilder::with_isa` | 1 | 1 | `crates/zed-native/src/lib.rs:144` | row S.4 |
| `cranelift_jit::backend::JITModule::finalize_definitions` | 1 | 1 | `crates/zed-native/src/lib.rs:151` | row S.4 |
| `cranelift_jit::backend::JITModule::free_memory` | 1 | 1 | `crates/zed-native/src/lib.rs:100` | row S.4 |
| `cranelift_jit::backend::JITModule::get_finalized_function` | 1 | 1 | `crates/zed-native/src/lib.rs:153` | row S.4 |
| `cranelift_jit::backend::JITModule::new` | 1 | 1 | `crates/zed-native/src/lib.rs:149` | row S.4 |
| `cranelift_jit::memory::system::SystemMemoryProvider::new` | 1 | 1 | `crates/zed-native/src/lib.rs:120` | row S.4 |
| `cranelift_module::data_context::DataDescription::define` | 1 | 1 | `crates/zed-native/src/exe.rs:105` | row S.4 |
| `cranelift_module::data_context::DataDescription::new` | 1 | 1 | `crates/zed-native/src/exe.rs:104` | row S.4 |
| `cranelift_module::default_libcall_names` | 4 | 1 | `crates/zed-native/src/lib.rs:26` | row S.4 |
| `cranelift_module::module::<&mut M as Module>::clear_context` | 2 | 2 | `crates/zed-native/src/codegen.rs:199` | row S.4 |
| `cranelift_module::module::<&mut M as Module>::declare_data_in_func` | 1 | 1 | `crates/zed-native/src/exe.rs:128` | row S.4 |
| `cranelift_module::module::<&mut M as Module>::isa` | 2 | 2 | `crates/zed-native/src/codegen.rs:195` | row S.4 |
| `cranelift_module::module::<&mut M as Module>::make_context` | 2 | 2 | `crates/zed-native/src/codegen.rs:170` | row S.4 |
| `cranelift_module::module::<&mut M as Module>::make_signature` | 1 | 1 | `crates/zed-native/src/exe.rs:108` | row S.4 |
| `cranelift_module::module::<&mut M as Module>::target_config` | 1 | 1 | `crates/zed-native/src/exe.rs:107` | row S.4 |
| `cranelift_module::module::Module::declare_data` | 1 | 1 | `crates/zed-native/src/exe.rs:102` | row S.4 |
| `cranelift_module::module::Module::declare_func_in_func` | 3 | 2 | `crates/zed-native/src/codegen.rs:277` | row S.4 |
| `cranelift_module::module::Module::declare_function` | 6 | 2 | `crates/zed-native/src/codegen.rs:125` | row S.4 |
| `cranelift_module::module::Module::define_data` | 1 | 1 | `crates/zed-native/src/exe.rs:106` | row S.4 |
| `cranelift_module::module::Module::define_function` | 2 | 2 | `crates/zed-native/src/codegen.rs:198` | row S.4 |
| `cranelift_module::module::Module::make_signature` | 1 | 1 | `crates/zed-native/src/codegen.rs:58` | row S.4 |
| `cranelift_native::builder` | 1 | 1 | `crates/zed-native/src/lib.rs:81` | row S.4 |
| `cranelift_object::backend::ObjectBuilder::new` | 1 | 1 | `crates/zed-native/src/lib.rs:200` | row S.4 |
| `cranelift_object::backend::ObjectModule::finish` | 2 | 1 | `crates/zed-native/src/lib.rs:172` | row S.4 |
| `cranelift_object::backend::ObjectModule::new` | 1 | 1 | `crates/zed-native/src/lib.rs:202` | row S.4 |
| `cranelift_object::backend::ObjectProduct::emit` | 2 | 1 | `crates/zed-native/src/lib.rs:172` | row S.4 |
| `imbl::hash::map::<GenericHashMap<K, V, S, P> as Clone>::clone` | 7 | 3 | `crates/zedc-preimage/src/preimage.rs:3350` | `x` |
| `imbl::hash::map::GenericHashMap<K, V, S, P>::get` | 5 | 3 | `crates/zedc-preimage/src/preimage.rs:2439` | `xs[i]` |
| `imbl::hash::map::GenericHashMap<K, V, S, P>::insert` | 3 | 3 | `crates/zedc-preimage/src/preimage.rs:3354` | row STD-seq |
| `imbl::hash::map::GenericHashMap<K, V, S, P>::new` | 8 | 3 | `crates/zedc-preimage/src/preimage.rs:2370` | `{}` |
| `imbl::hash::map::GenericHashMap<K, V, S, P>::update` | 4 | 2 | `crates/zedc-preimage/src/preimage.rs:2539` | row STD-seq |
| `imbl::hash::set::GenericHashSet<A, S, P>::contains` | 3 | 1 | `crates/zedc-presburger/src/presburger.rs:3120` | `k in m` |
| `imbl::hash::set::GenericHashSet<A, S, P>::insert` | 2 | 1 | `crates/zedc-presburger/src/presburger.rs:3134` | row STD-seq |
| `imbl::ord::map::<DiffIter<'a, 'b, K, V, P> as Iterator>::next` | 2 | 2 | `crates/zed-kernel/src/types.rs:1431` | row STD-seq |
| `imbl::ord::map::<GenericOrdMap<K, V, P> as Clone>::clone` | 23 | 8 | `crates/zed-kernel/src/provenance.rs:476` | `x` |
| `imbl::ord::map::<GenericOrdMap<K, V, P> as Extend<(RK, RV)>>::extend` | 3 | 2 | `crates/zed-kernel/src/value.rs:1016` | row L6.13 |
| `imbl::ord::map::<GenericOrdMap<K, V, P> as Index<&Q>>::index` | 6 | 2 | `crates/zedc-preimage/src/product.rs:892` | `xs[i]` |
| `imbl::ord::map::<GenericOrdMap<K, V, P> as PartialEq<Self>>::eq` | 3 | 1 | `crates/zedc-preimage/src/product.rs:1793` | `a == b` |
| `imbl::ord::map::<Iter<'a, K, V, P> as Iterator>::next` | 6 | 2 | `crates/zed-kernel/src/types.rs:1425` | row STD-seq |
| `imbl::ord::map::<RangedIter<'a, K, V, P> as Iterator>::next` | 2 | 1 | `crates/zed-kernel/src/types/bdd.rs:1878` | row L5.8a |
| `imbl::ord::map::Entry<'a, K, V, P>::or_default` | 8 | 3 | `crates/zedc-presburger/src/conjuncts.rs:33` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::contains_key` | 29 | 10 | `crates/zed-kernel/src/provenance.rs:509` | `k in m` |
| `imbl::ord::map::GenericOrdMap<K, V, P>::diff` | 22 | 6 | `crates/zed-kernel/src/provenance.rs:459` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::entry` | 8 | 3 | `crates/zedc-presburger/src/conjuncts.rs:33` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::get` | 109 | 13 | `crates/zed-kernel/src/eval.rs:139` | `xs[i]` |
| `imbl::ord::map::GenericOrdMap<K, V, P>::get_key_value` | 1 | 1 | `crates/zedc-preimage/src/product.rs:975` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::get_min` | 1 | 1 | `crates/zed-kernel/src/value.rs:1093` | `xs.first` |
| `imbl::ord::map::GenericOrdMap<K, V, P>::get_mut` | 15 | 3 | `crates/zedc-preimage/src/product.rs:1615` | missing |
| `imbl::ord::map::GenericOrdMap<K, V, P>::insert` | 70 | 12 | `crates/zed-kernel/src/eval.rs:134` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::is_empty` | 11 | 8 | `crates/zed-kernel/src/provenance.rs:334` | `xs.count == 0` |
| `imbl::ord::map::GenericOrdMap<K, V, P>::iter` | 25 | 9 | `crates/zed-kernel/src/provenance.rs:566` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::keys` | 14 | 6 | `crates/zed-kernel/src/provenance.rs:472` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::len` | 34 | 8 | `crates/zed-kernel/src/provenance.rs:340` | `xs.count` |
| `imbl::ord::map::GenericOrdMap<K, V, P>::new` | 30 | 9 | `crates/zed-kernel/src/provenance.rs:327` | `{}` |
| `imbl::ord::map::GenericOrdMap<K, V, P>::ptr_eq` | 1 | 1 | `crates/zed-kernel/src/value.rs:1210` | missing |
| `imbl::ord::map::GenericOrdMap<K, V, P>::range` | 3 | 2 | `crates/zed-kernel/src/types/bdd.rs:1874` | row L5.8a |
| `imbl::ord::map::GenericOrdMap<K, V, P>::remove` | 52 | 6 | `crates/zed-kernel/src/provenance.rs:525` | row STD-seq |
| `imbl::ord::map::GenericOrdMap<K, V, P>::values` | 8 | 4 | `crates/zed-kernel/src/provenance.rs:422` | row STD-seq |
| `imbl::ord::set::<DiffIter<'a, 'b, A, P> as Iterator>::next` | 1 | 1 | `crates/zedc-types/src/ty.rs:901` | row STD-seq |
| `imbl::ord::set::<GenericOrdSet<A, P> as Clone>::clone` | 8 | 5 | `crates/zed-kernel/src/types/bdd.rs:1472` | `x` |
| `imbl::ord::set::<GenericOrdSet<A, P> as Extend<R>>::extend` | 1 | 1 | `crates/zedc-presburger/src/conjuncts.rs:1304` | row L6.13 |
| `imbl::ord::set::<GenericOrdSet<A, P> as IntoIterator>::into_iter` | 1 | 1 | `crates/zedc-check/src/check/mod.rs:2553` | row STD-seq |
| `imbl::ord::set::<GenericOrdSet<A, P> as PartialEq<Self>>::eq` | 3 | 1 | `crates/zedc-presburger/src/conjuncts.rs:220` | `a == b` |
| `imbl::ord::set::<Iter<'a, A, P> as Iterator>::next` | 2 | 2 | `crates/zed-kernel/src/types/empty.rs:2831` | row STD-seq |
| `imbl::ord::set::GenericOrdSet<A, P>::contains` | 41 | 9 | `crates/zed-kernel/src/types.rs:1216` | `k in m` |
| `imbl::ord::set::GenericOrdSet<A, P>::diff` | 8 | 2 | `crates/zedc-preimage/src/product.rs:1086` | row STD-seq |
| `imbl::ord::set::GenericOrdSet<A, P>::insert` | 20 | 7 | `crates/zed-kernel/src/types.rs:1241` | row STD-seq |
| `imbl::ord::set::GenericOrdSet<A, P>::is_empty` | 18 | 6 | `crates/zed-kernel/src/types.rs:1145` | `xs.count == 0` |
| `imbl::ord::set::GenericOrdSet<A, P>::iter` | 38 | 9 | `crates/zed-kernel/src/types.rs:835` | row STD-seq |
| `imbl::ord::set::GenericOrdSet<A, P>::len` | 27 | 5 | `crates/zed-kernel/src/types.rs:1215` | `xs.count` |
| `imbl::ord::set::GenericOrdSet<A, P>::new` | 7 | 5 | `crates/zed-kernel/src/types/bdd.rs:1494` | `{}` |
| `imbl::ord::set::GenericOrdSet<A, P>::range` | 1 | 1 | `crates/zedc-presburger/src/conjuncts.rs:85` | missing |
| `imbl::ord::set::GenericOrdSet<A, P>::remove` | 11 | 3 | `crates/zed-kernel/src/types.rs:1247` | row STD-seq |
| `imbl::ord::set::GenericOrdSet<A, P>::unit` | 2 | 1 | `crates/zedc-presburger/src/conjuncts.rs:1354` | row STD-seq |
| `imbl::ord::set::GenericOrdSet<A, P>::update` | 1 | 1 | `crates/zed-kernel/src/types/bdd/list.rs:236` | missing |
| `imbl::ord::set::GenericOrdSet<A, P>::without` | 1 | 1 | `crates/zed-kernel/src/types/bdd/list.rs:262` | missing |
| `imbl::vector::<GenericVector<A, P> as Clone>::clone` | 9 | 3 | `crates/zed-kernel/src/eval.rs:804` | `x` |
| `imbl::vector::<GenericVector<A, P> as Extend<A>>::extend` | 1 | 1 | `crates/zed-kernel/src/eval.rs:440` | row L6.13 |
| `imbl::vector::<GenericVector<A, P> as Index<usize>>::index` | 32 | 1 | `crates/zedc-resolve/src/resolve.rs:750` | `xs[i]` |
| `imbl::vector::GenericVector<A, P>::append` | 1 | 1 | `crates/zedc-resolve/src/resolve.rs:915` | row L6.13 |
| `imbl::vector::GenericVector<A, P>::front` | 1 | 1 | `crates/zedc-resolve/src/resolve/tables.rs:48` | `xs.first` |
| `imbl::vector::GenericVector<A, P>::iter` | 3 | 2 | `crates/zed-kernel/src/provenance.rs:201` | row STD-seq |
| `imbl::vector::GenericVector<A, P>::last` | 1 | 1 | `crates/zed-kernel/src/provenance.rs:184` | `xs.last` |
| `imbl::vector::GenericVector<A, P>::len` | 21 | 7 | `crates/zed-kernel/src/eval.rs:371` | `xs.count` |
| `imbl::vector::GenericVector<A, P>::new` | 2 | 2 | `crates/zedc-preimage/src/product.rs:3228` | `[]` |
| `imbl::vector::GenericVector<A, P>::pop_back` | 1 | 1 | `crates/zed-kernel/src/eval.rs:770` | row STD-seq |
| `imbl::vector::GenericVector<A, P>::ptr_eq` | 1 | 1 | `crates/zedc-resolve/src/resolve/tables.rs:54` | missing |
| `imbl::vector::GenericVector<A, P>::push_back` | 5 | 2 | `crates/zed-kernel/src/eval.rs:729` | row L6.13 |
| `imbl::vector::GenericVector<A, P>::truncate` | 5 | 1 | `crates/zed-kernel/src/eval.rs:385` | missing |
| `imbl::vector::GenericVector<A, P>::unit` | 1 | 1 | `crates/zedc-preimage/src/product.rs:3227` | row STD-seq |
| `libc::mmap` | 1 | 1 | `crates/zed-native/src/lib.rs:359` | row S.4 |
| `libc::mprotect` | 1 | 1 | `crates/zed-native/src/lib.rs:379` | row S.4 |
| `libc::munmap` | 1 | 1 | `crates/zed-native/src/lib.rs:436` | row S.4 |
| `num_bigint::bigint::<&BigInt as Neg>::neg` | 10 | 3 | `crates/zed-kernel/src/num.rs:608` | `-a` |
| `num_bigint::bigint::<BigInt as Clone>::clone` | 32 | 2 | `crates/zed-kernel/src/num.rs:166` | `x` |
| `num_bigint::bigint::<BigInt as Integer>::div_ceil` | 2 | 1 | `crates/zedc-int/src/int.rs:549` | `if b < 0 { -(a div (-b)) } else { -((-a) div b) }` |
| `num_bigint::bigint::<BigInt as Integer>::div_floor` | 4 | 1 | `crates/zedc-int/src/int.rs:183` | `if b < 0 { (-a) div (-b) } else { a div b }` |
| `num_bigint::bigint::<BigInt as Integer>::gcd` | 5 | 1 | `crates/zedc-int/src/int.rs:171` | row STD-num |
| `num_bigint::bigint::<BigInt as Integer>::is_even` | 1 | 1 | `crates/zed-kernel/src/num.rs:244` | `a mod 2 == 0` |
| `num_bigint::bigint::<BigInt as Integer>::is_multiple_of` | 1 | 1 | `crates/zedc-int/src/int.rs:543` | `a mod b == 0` |
| `num_bigint::bigint::<BigInt as Integer>::is_odd` | 2 | 1 | `crates/zedc-int/src/int.rs:141` | `a mod 2 == 1` |
| `num_bigint::bigint::<BigInt as Integer>::mod_floor` | 5 | 1 | `crates/zedc-int/src/int.rs:194` | `if b < 0 { -((-a) mod (-b)) } else { a mod b }` |
| `num_bigint::bigint::<BigInt as Neg>::neg` | 10 | 6 | `crates/zed-kernel/src/eval.rs:2199` | `-a` |
| `num_bigint::bigint::<BigInt as One>::is_one` | 11 | 2 | `crates/zed-kernel/src/num.rs:61` | `a == 1` |
| `num_bigint::bigint::<BigInt as One>::one` | 12 | 3 | `crates/zed-kernel/src/bits.rs:252` | `1` |
| `num_bigint::bigint::<BigInt as Ord>::cmp` | 3 | 3 | `crates/zed-kernel/src/num.rs:1422` | missing |
| `num_bigint::bigint::<BigInt as PartialEq<Self>>::eq` | 24 | 2 | `crates/zed-kernel/src/num.rs:1490` | `a == b` |
| `num_bigint::bigint::<BigInt as Signed>::abs` | 1 | 1 | `crates/zed-kernel/src/num.rs:391` | `abs(a)` |
| `num_bigint::bigint::<BigInt as Signed>::is_negative` | 8 | 2 | `crates/zed-kernel/src/num.rs:192` | `a < 0` |
| `num_bigint::bigint::<BigInt as Signed>::is_positive` | 3 | 1 | `crates/zed-kernel/src/num.rs:248` | `a > 0` |
| `num_bigint::bigint::<BigInt as Zero>::is_zero` | 19 | 3 | `crates/zed-kernel/src/num.rs:50` | `a == 0` |
| `num_bigint::bigint::<BigInt as Zero>::zero` | 9 | 3 | `crates/zed-kernel/src/num.rs:713` | `0` |
| `num_bigint::bigint::<Sign as Ord>::cmp` | 2 | 2 | `crates/zed-kernel/src/num.rs:1424` | missing |
| `num_bigint::bigint::<Sign as PartialEq<Self>>::eq` | 48 | 5 | `crates/zed-kernel/src/num.rs:299` | `a == b` |
| `num_bigint::bigint::BigInt::bit` | 1 | 1 | `crates/zed-kernel/src/num/fast.rs:924` | missing |
| `num_bigint::bigint::BigInt::bits` | 42 | 3 | `crates/zed-kernel/src/num.rs:255` | row STD-num |
| `num_bigint::bigint::BigInt::from_biguint` | 11 | 6 | `crates/zed-kernel/src/num.rs:158` | `n * a` |
| `num_bigint::bigint::BigInt::into_parts` | 5 | 3 | `crates/zed-kernel/src/num.rs:736` | missing |
| `num_bigint::bigint::BigInt::iter_u64_digits` | 1 | 1 | `crates/zed-kernel/src/num/fast.rs:1018` | missing |
| `num_bigint::bigint::BigInt::magnitude` | 76 | 6 | `crates/zed-kernel/src/bits.rs:145` | `abs(a)` |
| `num_bigint::bigint::BigInt::nth_root` | 1 | 1 | `crates/zedc-int/src/int.rs:2155` | row STD-num |
| `num_bigint::bigint::BigInt::pow` | 1 | 1 | `crates/zedc-int/src/int.rs:2156` | `a^n` |
| `num_bigint::bigint::BigInt::sign` | 26 | 5 | `crates/zed-kernel/src/num.rs:299` | missing |
| `num_bigint::bigint::BigInt::to_biguint` | 1 | 1 | `crates/zed-kernel/src/num.rs:427` | missing |
| `num_bigint::bigint::BigInt::trailing_zeros` | 9 | 3 | `crates/zed-kernel/src/num.rs:1107` | missing |
| `num_bigint::bigint::addition::<&BigInt as Add<BigInt>>::add` | 12 | 2 | `crates/zed-kernel/src/num/fast.rs:969` | `a + b` |
| `num_bigint::bigint::addition::<&BigInt as Add<Self>>::add` | 27 | 3 | `crates/zed-kernel/src/num.rs:463` | `a + b` |
| `num_bigint::bigint::addition::<&BigInt as Add<u32>>::add` | 9 | 1 | `crates/zedc-int/src/int.rs:455` | `a + b` |
| `num_bigint::bigint::addition::<&BigInt as Add<u64>>::add` | 21 | 2 | `crates/zed-kernel/src/num/bound.rs:97` | `a + b` |
| `num_bigint::bigint::addition::<BigInt as Add<&BigInt>>::add` | 9 | 1 | `crates/zedc-int/src/int.rs:523` | `a + b` |
| `num_bigint::bigint::addition::<BigInt as Add<Self>>::add` | 36 | 3 | `crates/zed-kernel/src/num.rs:454` | `a + b` |
| `num_bigint::bigint::addition::<BigInt as Add<u32>>::add` | 3 | 1 | `crates/zedc-int/src/int.rs:2157` | `a + b` |
| `num_bigint::bigint::addition::<BigInt as AddAssign<Self>>::add_assign` | 15 | 3 | `crates/zed-kernel/src/num.rs:257` | `a + b` |
| `num_bigint::bigint::addition::<BigInt as AddAssign<u32>>::add_assign` | 3 | 1 | `crates/zedc-int/src/int.rs:481` | `a + b` |
| `num_bigint::bigint::addition::<BigInt as AddAssign<u64>>::add_assign` | 9 | 3 | `crates/zed-kernel/src/num.rs:97` | `a + b` |
| `num_bigint::bigint::bits::<&BigInt as BitAnd<BigInt>>::bitand` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:923` | missing |
| `num_bigint::bigint::bits::<&BigInt as BitAnd<Self>>::bitand` | 6 | 1 | `crates/zed-kernel/src/num/fast.rs:967` | missing |
| `num_bigint::bigint::convert::<BigInt as From<BigUint>>::from` | 37 | 6 | `crates/zed-kernel/src/bits.rs:236` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<i128>>::from` | 3 | 2 | `crates/zed-kernel/src/num/fast.rs:1058` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<i32>>::from` | 6 | 3 | `crates/zed-kernel/src/bits.rs:145` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<i64>>::from` | 10 | 5 | `crates/zed-kernel/src/eval.rs:2199` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<u128>>::from` | 1 | 1 | `crates/zedc-int/src/int.rs:169` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<u32>>::from` | 7 | 1 | `crates/zedc-int/src/int.rs:559` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<u64>>::from` | 13 | 4 | `crates/zed-kernel/src/bits.rs:50` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as From<usize>>::from` | 1 | 1 | `crates/zed-kernel/src/words.rs:122` | `int(a)` |
| `num_bigint::bigint::convert::<BigInt as ToPrimitive>::to_i64` | 3 | 2 | `crates/zed-kernel/src/num/bound.rs:105` | missing |
| `num_bigint::bigint::convert::<BigInt as ToPrimitive>::to_u64` | 2 | 1 | `crates/zed-kernel/src/num/bound.rs:118` | missing |
| `num_bigint::bigint::convert::<i128 as TryFrom<&BigInt>>::try_from` | 3 | 1 | `crates/zedc-int/src/int.rs:88` | missing |
| `num_bigint::bigint::convert::<i64 as TryFrom<&BigInt>>::try_from` | 2 | 1 | `crates/zedc-int/src/int.rs:1674` | missing |
| `num_bigint::bigint::convert::<u64 as TryFrom<&BigInt>>::try_from` | 5 | 1 | `crates/zedc-int/src/int.rs:395` | missing |
| `num_bigint::bigint::division::<BigInt as Div<&BigInt>>::div` | 6 | 1 | `crates/zedc-int/src/int.rs:1810` | `if (a < 0) != (b < 0) { -(abs(a) div abs(b)) } else { abs(a) div abs(b) }` |
| `num_bigint::bigint::division::<BigInt as Div<Self>>::div` | 15 | 1 | `crates/zedc-int/src/int.rs:544` | `if (a < 0) != (b < 0) { -(abs(a) div abs(b)) } else { abs(a) div abs(b) }` |
| `num_bigint::bigint::multiplication::<&BigInt as Mul<BigInt>>::mul` | 15 | 2 | `crates/zed-kernel/src/num.rs:534` | `a * b` |
| `num_bigint::bigint::multiplication::<&BigInt as Mul<Self>>::mul` | 78 | 2 | `crates/zed-kernel/src/num.rs:482` | `a * b` |
| `num_bigint::bigint::multiplication::<&BigInt as Mul<u32>>::mul` | 3 | 1 | `crates/zed-kernel/src/num.rs:257` | `a * b` |
| `num_bigint::bigint::multiplication::<&BigInt as Mul<u64>>::mul` | 3 | 1 | `crates/zed-kernel/src/num.rs:674` | `a * b` |
| `num_bigint::bigint::multiplication::<BigInt as Mul<&BigInt>>::mul` | 6 | 1 | `crates/zed-kernel/src/num.rs:537` | `a * b` |
| `num_bigint::bigint::multiplication::<BigInt as Mul<Self>>::mul` | 3 | 1 | `crates/zed-kernel/src/num.rs:1582` | `a * b` |
| `num_bigint::bigint::multiplication::<BigInt as MulAssign<Self>>::mul_assign` | 3 | 1 | `crates/zed-kernel/src/num.rs:236` | `a * b` |
| `num_bigint::bigint::multiplication::<Sign as Mul<Self>>::mul` | 6 | 1 | `crates/zed-kernel/src/num/fast.rs:576` | missing |
| `num_bigint::bigint::multiplication::<i32 as Mul<BigInt>>::mul` | 6 | 1 | `crates/zed-kernel/src/num.rs:994` | `a * b` |
| `num_bigint::bigint::power::<BigInt as Pow<&BigUint>>::pow` | 1 | 1 | `crates/zed-kernel/src/num.rs:236` | `a^n` |
| `num_bigint::bigint::power::<BigInt as Pow<u32>>::pow` | 2 | 1 | `crates/zed-kernel/src/num.rs:1582` | `a^n` |
| `num_bigint::bigint::shift::<&BigInt as Shl<u32>>::shl` | 3 | 1 | `crates/zedc-int/src/int.rs:1127` | `shl(a, n)` |
| `num_bigint::bigint::shift::<&BigInt as Shl<u64>>::shl` | 21 | 2 | `crates/zed-kernel/src/num/fast.rs:923` | `shl(a, n)` |
| `num_bigint::bigint::shift::<&BigInt as Shr<u64>>::shr` | 18 | 2 | `crates/zed-kernel/src/num/fast.rs:962` | `shr(a, n)` |
| `num_bigint::bigint::shift::<BigInt as Shl<u32>>::shl` | 6 | 1 | `crates/zedc-int/src/int.rs:1821` | `shl(a, n)` |
| `num_bigint::bigint::shift::<BigInt as Shl<u64>>::shl` | 15 | 2 | `crates/zed-kernel/src/num/fast.rs:925` | `shl(a, n)` |
| `num_bigint::bigint::shift::<BigInt as Shr<u32>>::shr` | 6 | 1 | `crates/zedc-int/src/int.rs:1256` | `shr(a, n)` |
| `num_bigint::bigint::shift::<BigInt as Shr<u64>>::shr` | 12 | 2 | `crates/zed-kernel/src/num.rs:1108` | `shr(a, n)` |
| `num_bigint::bigint::shift::<BigInt as ShrAssign<u64>>::shr_assign` | 6 | 1 | `crates/zedc-int/src/int.rs:478` | `shr(a, n)` |
| `num_bigint::bigint::subtraction::<&BigInt as Sub<BigInt>>::sub` | 3 | 1 | `crates/zedc-int/src/int.rs:1385` | `a - b` |
| `num_bigint::bigint::subtraction::<&BigInt as Sub<Self>>::sub` | 42 | 3 | `crates/zed-kernel/src/num.rs:424` | `a - b` |
| `num_bigint::bigint::subtraction::<&BigInt as Sub<i32>>::sub` | 3 | 1 | `crates/zed-kernel/src/num/bound.rs:247` | `a - b` |
| `num_bigint::bigint::subtraction::<&BigInt as Sub<u64>>::sub` | 3 | 1 | `crates/zedc-int/src/int.rs:1240` | `a - b` |
| `num_bigint::bigint::subtraction::<BigInt as Sub<&BigInt>>::sub` | 15 | 3 | `crates/zed-kernel/src/num.rs:526` | `a - b` |
| `num_bigint::bigint::subtraction::<BigInt as Sub<Self>>::sub` | 12 | 3 | `crates/zed-kernel/src/num.rs:398` | `a - b` |
| `num_bigint::bigint::subtraction::<BigInt as Sub<i32>>::sub` | 6 | 2 | `crates/zed-kernel/src/num.rs:255` | `a - b` |
| `num_bigint::bigint::subtraction::<BigInt as Sub<u64>>::sub` | 9 | 3 | `crates/zed-kernel/src/num.rs:165` | `a - b` |
| `num_bigint::bigint::subtraction::<BigInt as SubAssign<&BigInt>>::sub_assign` | 3 | 1 | `crates/zedc-int/src/int.rs:1128` | `a - b` |
| `num_bigint::bigint::subtraction::<BigInt as SubAssign<u64>>::sub_assign` | 3 | 1 | `crates/zed-kernel/src/num.rs:100` | `a - b` |
| `num_bigint::biguint::<BigUint as Clone>::clone` | 58 | 7 | `crates/zed-kernel/src/bits.rs:232` | `x` |
| `num_bigint::biguint::<BigUint as Integer>::div_rem` | 7 | 3 | `crates/zed-kernel/src/num/bound.rs:86` | `(a div b, a mod b)` |
| `num_bigint::biguint::<BigUint as Integer>::gcd` | 5 | 2 | `crates/zed-kernel/src/num/fast.rs:1079` | row STD-num |
| `num_bigint::biguint::<BigUint as Integer>::is_multiple_of` | 2 | 1 | `crates/zedc-int/src/int.rs:1065` | `a mod b == 0` |
| `num_bigint::biguint::<BigUint as Integer>::lcm` | 1 | 1 | `crates/zedc-int/src/int.rs:2354` | row STD-num |
| `num_bigint::biguint::<BigUint as One>::is_one` | 19 | 3 | `crates/zed-kernel/src/num.rs:668` | `a == 1` |
| `num_bigint::biguint::<BigUint as One>::one` | 16 | 4 | `crates/zed-kernel/src/num.rs:1161` | `1` |
| `num_bigint::biguint::<BigUint as Ord>::cmp` | 7 | 3 | `crates/zed-kernel/src/num/bound.rs:108` | missing |
| `num_bigint::biguint::<BigUint as PartialEq<Self>>::eq` | 27 | 4 | `crates/zed-kernel/src/num/bound.rs:263` | `a == b` |
| `num_bigint::biguint::<BigUint as Zero>::is_zero` | 25 | 5 | `crates/zed-kernel/src/num.rs:639` | `a == 0` |
| `num_bigint::biguint::<BigUint as Zero>::zero` | 7 | 4 | `crates/zed-kernel/src/num.rs:1289` | `0` |
| `num_bigint::biguint::BigUint::bit` | 6 | 3 | `crates/zed-kernel/src/num.rs:691` | row STD-num |
| `num_bigint::biguint::BigUint::bits` | 49 | 5 | `crates/zed-kernel/src/bits.rs:244` | row STD-num |
| `num_bigint::biguint::BigUint::count_ones` | 1 | 1 | `crates/zed-kernel/src/bits.rs:242` | `popCount(a)` |
| `num_bigint::biguint::BigUint::from_bytes_le` | 1 | 1 | `crates/zedc-zir/src/zir/binary.rs:604` | row STD-num |
| `num_bigint::biguint::BigUint::from_slice` | 2 | 2 | `crates/zed-kernel/src/num.rs:1298` | missing |
| `num_bigint::biguint::BigUint::iter_u32_digits` | 1 | 1 | `crates/zed-kernel/src/num/fast.rs:662` | missing |
| `num_bigint::biguint::BigUint::iter_u64_digits` | 23 | 4 | `crates/zed-kernel/src/num.rs:1237` | missing |
| `num_bigint::biguint::BigUint::modpow` | 4 | 2 | `crates/zed-kernel/src/num.rs:753` | row STD-num |
| `num_bigint::biguint::BigUint::new` | 2 | 1 | `crates/zed-kernel/src/num/fast.rs:527` | missing |
| `num_bigint::biguint::BigUint::nth_root` | 1 | 1 | `crates/zedc-int/src/int.rs:871` | row STD-num |
| `num_bigint::biguint::BigUint::parse_bytes` | 1 | 1 | `crates/zed-kernel/src/value.rs:482` | row STD-num |
| `num_bigint::biguint::BigUint::pow` | 2 | 2 | `crates/zed-kernel/src/num/fast.rs:1162` | `a^n` |
| `num_bigint::biguint::BigUint::sqrt` | 1 | 1 | `crates/zedc-int/src/int.rs:603` | row STD-num |
| `num_bigint::biguint::BigUint::to_u64_digits` | 1 | 1 | `crates/zed-kernel/src/num/fast.rs:705` | missing |
| `num_bigint::biguint::BigUint::trailing_zeros` | 11 | 5 | `crates/zed-kernel/src/bits.rs:247` | missing |
| `num_bigint::biguint::addition::<&BigUint as Add<Self>>::add` | 9 | 1 | `crates/zedc-int/src/int.rs:1038` | `a + b` |
| `num_bigint::biguint::addition::<&BigUint as Add<u32>>::add` | 12 | 3 | `crates/zed-kernel/src/num/bound.rs:267` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as Add<&BigUint>>::add` | 6 | 2 | `crates/zed-kernel/src/types/empty.rs:998` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as Add<Self>>::add` | 27 | 4 | `crates/zed-kernel/src/num.rs:292` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as Add<u32>>::add` | 24 | 5 | `crates/zed-kernel/src/num.rs:304` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as Add<u64>>::add` | 9 | 2 | `crates/zed-kernel/src/num.rs:531` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as AddAssign<&BigUint>>::add_assign` | 3 | 1 | `crates/zedc-presburger/src/presburger/deep/canon.rs:537` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as AddAssign<Self>>::add_assign` | 21 | 5 | `crates/zed-kernel/src/num.rs:1224` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as AddAssign<u32>>::add_assign` | 9 | 2 | `crates/zed-kernel/src/num/bound.rs:51` | `a + b` |
| `num_bigint::biguint::addition::<BigUint as AddAssign<u64>>::add_assign` | 3 | 1 | `crates/zedc-int/src/int.rs:1330` | missing |
| `num_bigint::biguint::bits::<&BigUint as BitAnd<Self>>::bitand` | 6 | 2 | `crates/zed-kernel/src/num/fast.rs:948` | `bitAnd(a, b)` |
| `num_bigint::biguint::bits::<&BigUint as BitOr<Self>>::bitor` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:1066` | missing |
| `num_bigint::biguint::bits::<BigUint as BitAnd<&BigUint>>::bitand` | 36 | 2 | `crates/zed-kernel/src/num/fast.rs:948` | `bitAnd(a, b)` |
| `num_bigint::biguint::bits::<BigUint as BitAnd<Self>>::bitand` | 12 | 3 | `crates/zed-kernel/src/bits.rs:237` | `bitAnd(a, b)` |
| `num_bigint::biguint::bits::<BigUint as BitOr<Self>>::bitor` | 3 | 1 | `crates/zed-kernel/src/bits.rs:238` | `bitOr(a, b)` |
| `num_bigint::biguint::bits::<BigUint as BitXor<Self>>::bitxor` | 3 | 1 | `crates/zed-kernel/src/bits.rs:239` | `bitXor(a, b)` |
| `num_bigint::biguint::convert::<BigUint as From<u128>>::from` | 1 | 1 | `crates/zed-kernel/src/num.rs:1270` | `int(a)` |
| `num_bigint::biguint::convert::<BigUint as From<u32>>::from` | 33 | 4 | `crates/zed-kernel/src/num.rs:181` | `int(a)` |
| `num_bigint::biguint::convert::<BigUint as From<u64>>::from` | 39 | 5 | `crates/zed-kernel/src/num.rs:460` | `int(a)` |
| `num_bigint::biguint::convert::<BigUint as From<usize>>::from` | 19 | 10 | `crates/zed-kernel/src/num.rs:156` | `int(a)` |
| `num_bigint::biguint::convert::<BigUint as ToPrimitive>::to_u128` | 1 | 1 | `crates/zed-kernel/src/words.rs:375` | missing |
| `num_bigint::biguint::convert::<BigUint as ToPrimitive>::to_u64` | 9 | 3 | `crates/zed-kernel/src/num.rs:365` | missing |
| `num_bigint::biguint::convert::<u128 as TryFrom<&BigUint>>::try_from` | 1 | 1 | `crates/zedc-int/src/int.rs:2005` | missing |
| `num_bigint::biguint::convert::<u32 as TryFrom<&BigUint>>::try_from` | 3 | 1 | `crates/zedc-int/src/int.rs:872` | missing |
| `num_bigint::biguint::convert::<u64 as TryFrom<&BigUint>>::try_from` | 3 | 1 | `crates/zedc-int/src/int.rs:1119` | missing |
| `num_bigint::biguint::convert::<u64 as TryFrom<BigUint>>::try_from` | 3 | 2 | `crates/zed-kernel/src/types/empty.rs:952` | missing |
| `num_bigint::biguint::division::<&BigUint as Div<Self>>::div` | 18 | 1 | `crates/zedc-int/src/int.rs:1065` | `a div b` |
| `num_bigint::biguint::division::<&BigUint as Rem<u32>>::rem` | 3 | 1 | `crates/zed-kernel/src/num.rs:1233` | `a mod b` |
| `num_bigint::biguint::division::<&BigUint as Rem<u64>>::rem` | 27 | 3 | `crates/zed-kernel/src/num.rs:364` | `a mod b` |
| `num_bigint::biguint::division::<BigUint as Div<&BigUint>>::div` | 9 | 1 | `crates/zedc-int/src/int.rs:883` | `a div b` |
| `num_bigint::biguint::division::<BigUint as Div<Self>>::div` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:852` | missing |
| `num_bigint::biguint::division::<BigUint as Rem<&BigUint>>::rem` | 9 | 2 | `crates/zed-kernel/src/num.rs:753` | `a mod b` |
| `num_bigint::biguint::division::<BigUint as RemAssign<Self>>::rem_assign` | 3 | 1 | `crates/zed-kernel/src/types/empty.rs:2579` | `a mod b` |
| `num_bigint::biguint::iter::<U64Digits<'_> as DoubleEndedIterator>::next_back` | 1 | 1 | `crates/zed-kernel/src/num/fast.rs:702` | missing |
| `num_bigint::biguint::iter::<U64Digits<'_> as ExactSizeIterator>::len` | 9 | 4 | `crates/zed-kernel/src/num.rs:1279` | `xs.count` |
| `num_bigint::biguint::iter::<U64Digits<'_> as Iterator>::next` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:938` | missing |
| `num_bigint::biguint::multiplication::<&BigUint as Mul<BigUint>>::mul` | 9 | 2 | `crates/zedc-int/src/int.rs:1094` | `a * b` |
| `num_bigint::biguint::multiplication::<&BigUint as Mul<Self>>::mul` | 42 | 3 | `crates/zed-kernel/src/num.rs:347` | `a * b` |
| `num_bigint::biguint::multiplication::<&BigUint as Mul<u32>>::mul` | 15 | 3 | `crates/zed-kernel/src/num.rs:304` | `a * b` |
| `num_bigint::biguint::multiplication::<&BigUint as Mul<u64>>::mul` | 9 | 2 | `crates/zed-kernel/src/types/empty.rs:956` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as Mul<&BigUint>>::mul` | 9 | 2 | `crates/zed-kernel/src/num.rs:661` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as Mul<Self>>::mul` | 16 | 2 | `crates/zed-kernel/src/num.rs:753` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as Mul<u32>>::mul` | 12 | 3 | `crates/zed-kernel/src/num.rs:1041` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as Mul<u64>>::mul` | 6 | 2 | `crates/zed-kernel/src/types/empty.rs:998` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as MulAssign<&BigUint>>::mul_assign` | 3 | 1 | `crates/zedc-int/src/int.rs:586` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as MulAssign<u32>>::mul_assign` | 3 | 1 | `crates/zedc-int/src/int.rs:608` | `a * b` |
| `num_bigint::biguint::multiplication::<BigUint as MulAssign<u64>>::mul_assign` | 9 | 2 | `crates/zed-kernel/src/types/empty.rs:957` | `a * b` |
| `num_bigint::biguint::power::<&BigUint as Pow<Self>>::pow` | 1 | 1 | `crates/zed-kernel/src/num.rs:686` | `a^n` |
| `num_bigint::biguint::power::<BigUint as Pow<u32>>::pow` | 1 | 1 | `crates/zed-kernel/src/num.rs:1054` | `a^n` |
| `num_bigint::biguint::shift::<&BigUint as Shl<u32>>::shl` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:705` | missing |
| `num_bigint::biguint::shift::<&BigUint as Shl<u64>>::shl` | 21 | 3 | `crates/zed-kernel/src/num/bound.rs:86` | `shl(a, n)` |
| `num_bigint::biguint::shift::<&BigUint as Shl<usize>>::shl` | 6 | 1 | `crates/zed-kernel/src/num/bound.rs:120` | `shl(a, n)` |
| `num_bigint::biguint::shift::<&BigUint as Shr<u32>>::shr` | 3 | 1 | `crates/zed-kernel/src/num/bound.rs:364` | `shr(a, n)` |
| `num_bigint::biguint::shift::<&BigUint as Shr<u64>>::shr` | 33 | 3 | `crates/zed-kernel/src/num/bound.rs:49` | `shr(a, n)` |
| `num_bigint::biguint::shift::<BigUint as Shl<u32>>::shl` | 90 | 11 | `crates/zed-kernel/src/num.rs:156` | `shl(a, n)` |
| `num_bigint::biguint::shift::<BigUint as Shl<u64>>::shl` | 36 | 3 | `crates/zed-kernel/src/num.rs:181` | `shl(a, n)` |
| `num_bigint::biguint::shift::<BigUint as Shl<usize>>::shl` | 6 | 2 | `crates/zed-kernel/src/num.rs:1298` | `shl(a, n)` |
| `num_bigint::biguint::shift::<BigUint as ShlAssign<u64>>::shl_assign` | 3 | 1 | `crates/zed-kernel/src/num/fast.rs:1238` | `shl(a, n)` |
| `num_bigint::biguint::shift::<BigUint as Shr<u32>>::shr` | 15 | 4 | `crates/zed-kernel/src/num.rs:304` | `shr(a, n)` |
| `num_bigint::biguint::shift::<BigUint as Shr<u64>>::shr` | 9 | 1 | `crates/zed-kernel/src/num/fast.rs:631` | missing |
| `num_bigint::biguint::shift::<BigUint as ShrAssign<u64>>::shr_assign` | 3 | 1 | `crates/zed-kernel/src/num/bound.rs:67` | `shr(a, n)` |
| `num_bigint::biguint::subtraction::<&BigUint as Sub<BigUint>>::sub` | 3 | 1 | `crates/zed-kernel/src/num.rs:1313` | `a - b` |
| `num_bigint::biguint::subtraction::<&BigUint as Sub<Self>>::sub` | 30 | 4 | `crates/zed-kernel/src/num.rs:1343` | `a - b` |
| `num_bigint::biguint::subtraction::<&BigUint as Sub<u32>>::sub` | 9 | 1 | `crates/zedc-int/src/int.rs:725` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as Sub<&BigUint>>::sub` | 3 | 1 | `crates/zed-kernel/src/types/empty.rs:2579` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as Sub<Self>>::sub` | 21 | 3 | `crates/zed-kernel/src/num/fast.rs:858` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as Sub<u32>>::sub` | 6 | 1 | `crates/zed-kernel/src/num/fast.rs:947` | missing |
| `num_bigint::biguint::subtraction::<BigUint as Sub<u64>>::sub` | 3 | 1 | `crates/zedc-int/src/int.rs:1502` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as Sub<u8>>::sub` | 3 | 1 | `crates/zedc-presburger/src/presburger/deep/canon.rs:439` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as SubAssign<&BigUint>>::sub_assign` | 9 | 2 | `crates/zed-kernel/src/num/fast.rs:829` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as SubAssign<u32>>::sub_assign` | 6 | 2 | `crates/zed-kernel/src/num/fast.rs:830` | `a - b` |
| `num_bigint::biguint::subtraction::<BigUint as SubAssign<u8>>::sub_assign` | 6 | 1 | `crates/zedc-presburger/src/presburger/deep/canon.rs:370` | `a - b` |
| `num_integer::<i128 as Integer>::div_floor` | 1 | 1 | `crates/zedc-int/src/int.rs:2216` | `if b < 0 { (-a) div (-b) } else { a div b }` |
| `num_integer::<i128 as Integer>::gcd` | 1 | 1 | `crates/zedc-int/src/int.rs:2304` | row STD-num |
| `num_integer::<i128 as Integer>::mod_floor` | 1 | 1 | `crates/zedc-int/src/int.rs:2266` | `if b < 0 { -((-a) mod (-b)) } else { a mod b }` |
| `num_traits::cast::ToPrimitive::to_usize` | 3 | 3 | `crates/zed-kernel/src/num.rs:1350` | missing |
| `object::read::any::<File<'data, R> as Object<'data>>::build_id` | 1 | 1 | `crates/zed-native/src/link.rs:778` | missing |
| `object::read::any::<Section<'data, 'file, R> as ObjectSection<'data>>::data` | 2 | 1 | `crates/zed-native/src/link.rs:346` | row S.4 |
| `object::read::any::<Section<'data, 'file, R> as ObjectSection<'data>>::file_range` | 1 | 1 | `crates/zed-native/src/link.rs:344` | missing |
| `object::read::any::File<'data, R>::parse` | 3 | 1 | `crates/zed-native/src/link.rs:342` | row S.4 |
| `object::read::archive::ArchiveFile<'data, R>::member` | 1 | 1 | `crates/zed-native/src/link.rs:887` | row S.4 |
| `object::read::archive::ArchiveFile<'data, R>::parse` | 1 | 1 | `crates/zed-native/src/link.rs:877` | row S.4 |
| `object::read::archive::ArchiveFile<'data, R>::symbols` | 1 | 1 | `crates/zed-native/src/link.rs:878` | row S.4 |
| `object::read::archive::ArchiveMember<'data>::file_range` | 1 | 1 | `crates/zed-native/src/link.rs:887` | row S.4 |
| `object::read::archive::ArchiveSymbol<'data>::name` | 1 | 1 | `crates/zed-native/src/link.rs:883` | row S.4 |
| `object::read::archive::ArchiveSymbol<'data>::offset` | 1 | 1 | `crates/zed-native/src/link.rs:887` | row S.4 |
| `object::read::read_cache::ReadCache<R>::new` | 4 | 1 | `crates/zed-native/src/link.rs:341` | row S.4 |
| `object::read::read_cache::ReadCache<R>::range` | 1 | 1 | `crates/zed-native/src/link.rs:888` | row S.4 |
| `object::read::traits::Object::section_by_name` | 2 | 1 | `crates/zed-native/src/link.rs:343` | row S.4 |
| `perf_event2::Counter::read` | 1 | 1 | `crates/zedc/src/main.rs:103` | missing |
| `perf_event2::builder::Builder<'a>::build` | 1 | 1 | `crates/zedc/src/main.rs:97` | missing |
| `perf_event2::builder::Builder<'a>::enabled` | 1 | 1 | `crates/zedc/src/main.rs:96` | missing |
| `perf_event2::builder::Builder<'a>::inherit` | 1 | 1 | `crates/zedc/src/main.rs:95` | missing |
| `perf_event2::builder::Builder<'a>::new` | 1 | 1 | `crates/zedc/src/main.rs:94` | missing |
| `std::collections::hash::map::<Drain<'a, K, V, A> as Iterator>::next` | 1 | 1 | `crates/zedc-preimage/src/preimage.rs:2451` | missing |
| `std::collections::hash::map::<HashMap<K, V, S, A> as Clone>::clone` | 7 | 1 | `crates/zedc/src/query.rs:119` | `x` |
| `std::collections::hash::map::<HashMap<K, V, S, A> as Index<&Q>>::index` | 90 | 20 | `crates/zed-kernel/src/provenance.rs:476` | `xs[i]` |
| `std::collections::hash::map::<HashMap<K, V, S, A> as IntoIterator>::into_iter` | 4 | 3 | `crates/zedc-check/src/check/arms.rs:349` | row STD-seq |
| `std::collections::hash::map::<HashMap<K, V> as From<[(K, V); N]>>::from` | 5 | 3 | `crates/zed-kernel/src/types.rs:2575` | missing |
| `std::collections::hash::map::Entry<'a, K, V, A>::or_insert` | 22 | 15 | `crates/zed-kernel/src/provenance.rs:406` | row STD-seq |
| `std::collections::hash::map::Entry<'a, K, V, A>::or_insert_with` | 20 | 14 | `crates/zed-kernel/src/eval.rs:423` | row STD-seq |
| `std::collections::hash::map::Entry<'a, K, V>::or_default` | 36 | 15 | `crates/zed-kernel/src/provenance.rs:291` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::clear` | 14 | 5 | `crates/zed-kernel/src/eval.rs:369` | row L6.13 |
| `std::collections::hash::map::HashMap<K, V, S, A>::contains_key` | 39 | 18 | `crates/zed-kernel/src/types.rs:2661` | `k in m` |
| `std::collections::hash::map::HashMap<K, V, S, A>::drain` | 1 | 1 | `crates/zedc-preimage/src/preimage.rs:2451` | missing |
| `std::collections::hash::map::HashMap<K, V, S, A>::entry` | 82 | 27 | `crates/zed-kernel/src/eval.rs:423` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::get` | 208 | 36 | `crates/zed-kernel/src/provenance.rs:264` | `xs[i]` |
| `std::collections::hash::map::HashMap<K, V, S, A>::get_key_value` | 1 | 1 | `crates/zedc-zir/src/zir/memory.rs:971` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::get_mut` | 14 | 10 | `crates/zed-kernel/src/types.rs:332` | row L6.13 |
| `std::collections::hash::map::HashMap<K, V, S, A>::insert` | 141 | 35 | `crates/zed-kernel/src/provenance.rs:277` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::is_empty` | 5 | 3 | `crates/zed-kernel/src/types/bdd.rs:1208` | `xs.count == 0` |
| `std::collections::hash::map::HashMap<K, V, S, A>::iter` | 1 | 1 | `crates/zed-kernel/src/types/bdd.rs:1139` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::keys` | 2 | 1 | `crates/zedc-presburger/src/presburger.rs:3542` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::len` | 32 | 10 | `crates/zed-kernel/src/types.rs:2581` | `xs.count` |
| `std::collections::hash::map::HashMap<K, V, S, A>::remove` | 35 | 11 | `crates/zed-kernel/src/types.rs:336` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::remove_entry` | 1 | 1 | `crates/zed-kernel/src/types/rec.rs:832` | missing |
| `std::collections::hash::map::HashMap<K, V, S, A>::retain` | 1 | 1 | `crates/zedc-preimage/src/preimage.rs:1068` | missing |
| `std::collections::hash::map::HashMap<K, V, S, A>::values` | 1 | 1 | `crates/zed-kernel/src/types/empty.rs:3914` | row STD-seq |
| `std::collections::hash::map::HashMap<K, V, S, A>::values_mut` | 1 | 1 | `crates/zedc-preimage/src/preimage.rs:2496` | missing |
| `std::collections::hash::map::HashMap<K, V>::new` | 139 | 36 | `crates/zed-kernel/src/provenance.rs:248` | `{}` |
| `std::collections::hash::map::HashMap<K, V>::with_capacity` | 4 | 4 | `crates/zed-kernel/src/types/bdd.rs:483` | row L6.13 |
| `std::collections::hash::map::OccupiedEntry<'a, K, V, A>::get` | 3 | 2 | `crates/zed-kernel/src/types/empty.rs:3707` | row STD-seq |
| `std::collections::hash::map::OccupiedEntry<'a, K, V, A>::get_mut` | 1 | 1 | `crates/zedc-check/src/check/mod.rs:1442` | row L6.13 |
| `std::collections::hash::map::OccupiedEntry<'a, K, V, A>::insert` | 1 | 1 | `crates/zed-kernel/src/types/rec.rs:599` | missing |
| `std::collections::hash::map::VacantEntry<'a, K, V, A>::insert` | 4 | 3 | `crates/zed-kernel/src/types/empty.rs:3705` | row STD-seq |
| `std::collections::hash::set::<HashSet<T, S, A> as Clone>::clone` | 3 | 3 | `crates/zed-kernel/src/types/empty.rs:351` | `x` |
| `std::collections::hash::set::<HashSet<T, S, A> as Extend<T>>::extend` | 6 | 4 | `crates/zed-kernel/src/types/debug.rs:61` | row L6.13 |
| `std::collections::hash::set::<HashSet<T> as From<[T; N]>>::from` | 1 | 1 | `crates/zed-kernel/src/types.rs:2097` | missing |
| `std::collections::hash::set::HashSet<T, S, A>::contains` | 44 | 17 | `crates/zed-kernel/src/types.rs:914` | `k in m` |
| `std::collections::hash::set::HashSet<T, S, A>::insert` | 98 | 30 | `crates/zed-kernel/src/provenance.rs:419` | row STD-seq |
| `std::collections::hash::set::HashSet<T, S, A>::is_empty` | 2 | 2 | `crates/zedc-check/src/check/walk.rs:2343` | `xs.count == 0` |
| `std::collections::hash::set::HashSet<T, S, A>::iter` | 4 | 2 | `crates/zedc-presburger/src/presburger.rs:2528` | row STD-seq |
| `std::collections::hash::set::HashSet<T, S, A>::len` | 1 | 1 | `crates/zedc-types/src/ty.rs:3657` | `xs.count` |
| `std::collections::hash::set::HashSet<T, S, A>::remove` | 4 | 2 | `crates/zedc-elab/src/elab/walk.rs:1366` | row STD-seq |
| `std::collections::hash::set::HashSet<T>::new` | 63 | 27 | `crates/zed-kernel/src/provenance.rs:313` | `{}` |
| `std::env::args_os` | 1 | 1 | `crates/zedc/src/main.rs:24` | missing |
| `std::env::current_dir` | 1 | 1 | `crates/zedc/src/suppress.rs:39` | missing |
| `std::env::current_exe` | 2 | 1 | `crates/zed-native/src/link.rs:109` | missing |
| `std::env::var_os` | 3 | 1 | `crates/zed-native/src/link.rs:72` | missing |
| `std::f64::f64::powf` | 1 | 1 | `crates/zed-kernel/src/eval.rs:2222` | missing |
| `std::ffi::os_str::<OsStr as ToOwned>::to_owned` | 4 | 1 | `crates/zed-native/src/link.rs:476` | `x` |
| `std::ffi::os_str::<OsString as Clone>::clone` | 1 | 1 | `crates/zed-native/src/link.rs:205` | missing |
| `std::ffi::os_str::<OsString as From<&T>>::from` | 1 | 1 | `crates/zed-native/src/link.rs:219` | missing |
| `std::ffi::os_str::OsStr::as_encoded_bytes` | 4 | 3 | `crates/zed-native/src/link.rs:624` | missing |
| `std::ffi::os_str::OsStr::is_empty` | 1 | 1 | `crates/zed-native/src/link.rs:611` | missing |
| `std::ffi::os_str::OsStr::len` | 1 | 1 | `crates/zed-native/src/sources.rs:134` | missing |
| `std::ffi::os_str::OsStr::to_str` | 3 | 2 | `crates/zedc/src/run.rs:778` | missing |
| `std::ffi::os_str::OsStr::to_string_lossy` | 4 | 2 | `crates/zed-native/src/exe.rs:188` | missing |
| `std::ffi::os_str::OsString::into_string` | 1 | 1 | `crates/zedc/src/main.rs:47` | missing |
| `std::ffi::os_str::OsString::push` | 5 | 1 | `crates/zed-native/src/link.rs:206` | row L6.13 |
| `std::fs::<File as Read>::read_to_end` | 1 | 1 | `crates/zed-native/src/sources.rs:159` | missing |
| `std::fs::DirEntry::file_name` | 1 | 1 | `crates/zed-native/src/link.rs:622` | missing |
| `std::fs::DirEntry::file_type` | 1 | 1 | `crates/zed-native/src/link.rs:631` | missing |
| `std::fs::DirEntry::path` | 3 | 2 | `crates/zed-native/src/link.rs:635` | missing |
| `std::fs::File::lock` | 1 | 1 | `crates/zed-native/src/link.rs:571` | missing |
| `std::fs::File::metadata` | 2 | 1 | `crates/zed-native/src/link.rs:443` | missing |
| `std::fs::File::open` | 8 | 2 | `crates/zed-native/src/link.rs:322` | missing |
| `std::fs::File::try_lock` | 1 | 1 | `crates/zed-native/src/link.rs:641` | missing |
| `std::fs::FileType::is_dir` | 1 | 1 | `crates/zed-native/src/link.rs:631` | missing |
| `std::fs::OpenOptions::new` | 1 | 1 | `crates/zed-native/src/link.rs:335` | missing |
| `std::fs::OpenOptions::open` | 1 | 1 | `crates/zed-native/src/link.rs:338` | missing |
| `std::fs::OpenOptions::read` | 1 | 1 | `crates/zed-native/src/link.rs:336` | missing |
| `std::fs::OpenOptions::write` | 1 | 1 | `crates/zed-native/src/link.rs:337` | missing |
| `std::fs::canonicalize` | 4 | 3 | `crates/zed-native/src/sources.rs:98` | missing |
| `std::fs::create_dir` | 1 | 1 | `crates/zed-native/src/link.rs:563` | missing |
| `std::fs::metadata` | 1 | 1 | `crates/zed-native/src/link.rs:432` | missing |
| `std::fs::read` | 9 | 5 | `crates/zed-native/src/link.rs:251` | missing |
| `std::fs::read_dir` | 3 | 2 | `crates/zed-native/src/link.rs:616` | missing |
| `std::fs::read_to_string` | 2 | 1 | `crates/zed-native/src/sources.rs:47` | missing |
| `std::fs::remove_dir_all` | 2 | 1 | `crates/zed-native/src/link.rs:587` | missing |
| `std::fs::rename` | 1 | 1 | `crates/zed-native/src/link.rs:291` | missing |
| `std::fs::symlink_metadata` | 1 | 1 | `crates/zed-native/src/link.rs:594` | missing |
| `std::fs::write` | 4 | 2 | `crates/zed-native/src/link.rs:215` | missing |
| `std::hash::random::<DefaultHasher as Hasher>::finish` | 1 | 1 | `crates/zedc-presburger/src/presburger/deep.rs:603` | missing |
| `std::hash::random::DefaultHasher::new` | 1 | 1 | `crates/zedc-presburger/src/presburger/deep.rs:583` | missing |
| `std::io::stdio::<Stdout as Write>::flush` | 1 | 1 | `crates/zed-native/src/exe.rs:170` | missing |
| `std::io::stdio::stderr` | 4 | 2 | `crates/zed-native/src/exe.rs:178` | missing |
| `std::io::stdio::stdin` | 2 | 2 | `crates/zed-native/src/exe.rs:178` | missing |
| `std::io::stdio::stdout` | 4 | 2 | `crates/zed-native/src/exe.rs:170` | missing |
| `std::macros::eprint!` | 1 | 1 | `crates/zedc/src/main.rs:29` | missing |
| `std::macros::eprintln!` | 8 | 3 | `crates/zedc-preimage/src/preimage.rs:8146` | missing |
| `std::macros::panic!` | 20 | 10 | `crates/zed-kernel/src/provenance.rs:241` | row S.1d |
| `std::macros::print!` | 1 | 1 | `crates/zedc/src/main.rs:61` | missing |
| `std::macros::println!` | 1 | 1 | `crates/zedc/src/main.rs:55` | missing |
| `std::os::unix::ffi::os_str::<OsStr as OsStrExt>::as_bytes` | 2 | 1 | `crates/zed-native/src/link.rs:489` | missing |
| `std::os::unix::ffi::os_str::<OsStr as OsStrExt>::from_bytes` | 3 | 1 | `crates/zed-native/src/link.rs:388` | missing |
| `std::os::unix::ffi::os_str::<OsString as OsStringExt>::from_vec` | 1 | 1 | `crates/zed-native/src/exe.rs:164` | missing |
| `std::os::unix::fs::<fs::Metadata as MetadataExt>::dev` | 4 | 1 | `crates/zed-native/src/link.rs:433` | missing |
| `std::os::unix::fs::<fs::Metadata as MetadataExt>::ino` | 4 | 1 | `crates/zed-native/src/link.rs:433` | missing |
| `std::os::unix::fs::FileExt::write_all_at` | 1 | 1 | `crates/zed-native/src/link.rs:356` | missing |
| `std::path::<PathBuf as Clone>::clone` | 5 | 2 | `crates/zed-native/src/sources.rs:71` | `x` |
| `std::path::<PathBuf as From<&T>>::from` | 2 | 1 | `crates/zed-native/src/link.rs:407` | missing |
| `std::path::<PathBuf as From<OsString>>::from` | 3 | 1 | `crates/zed-native/src/link.rs:113` | missing |
| `std::path::Component<'a>::as_os_str` | 2 | 2 | `crates/zedc/src/suppress.rs:61` | missing |
| `std::path::Path::ancestors` | 2 | 2 | `crates/zed-native/src/sources.rs:45` | missing |
| `std::path::Path::as_os_str` | 5 | 2 | `crates/zed-native/src/link.rs:476` | missing |
| `std::path::Path::components` | 6 | 3 | `crates/zed-native/src/sources.rs:172` | missing |
| `std::path::Path::display` | 33 | 4 | `crates/zed-native/src/link.rs:163` | missing |
| `std::path::Path::extension` | 1 | 1 | `crates/zed-native/src/sources.rs:150` | missing |
| `std::path::Path::file_name` | 3 | 1 | `crates/zed-native/src/link.rs:545` | missing |
| `std::path::Path::is_dir` | 1 | 1 | `crates/zed-native/src/sources.rs:105` | missing |
| `std::path::Path::is_file` | 4 | 3 | `crates/zed-native/src/link.rs:157` | missing |
| `std::path::Path::join` | 14 | 3 | `crates/zed-native/src/link.rs:207` | row STD-text |
| `std::path::Path::new` | 7 | 4 | `crates/zed-native/src/link.rs:131` | missing |
| `std::path::Path::parent` | 5 | 3 | `crates/zed-native/src/link.rs:610` | missing |
| `std::path::Path::strip_prefix` | 2 | 2 | `crates/zed-native/src/sources.rs:133` | row STD-text |
| `std::path::Path::symlink_metadata` | 1 | 1 | `crates/zed-native/src/link.rs:389` | missing |
| `std::path::Path::to_path_buf` | 3 | 3 | `crates/zed-native/src/link.rs:390` | missing |
| `std::path::Path::with_file_name` | 1 | 1 | `crates/zed-native/src/link.rs:110` | missing |
| `std::path::PathBuf::new` | 1 | 1 | `crates/zed-native/src/sources.rs:171` | missing |
| `std::path::PathBuf::pop` | 1 | 1 | `crates/zed-native/src/sources.rs:176` | missing |
| `std::path::PathBuf::push` | 1 | 1 | `crates/zed-native/src/sources.rs:178` | missing |
| `std::process::<ExitCode as From<u8>>::from` | 2 | 1 | `crates/zedc/src/main.rs:33` | missing |
| `std::process::Command::arg` | 8 | 1 | `crates/zed-native/src/link.rs:224` | missing |
| `std::process::Command::args` | 2 | 1 | `crates/zed-native/src/link.rs:228` | missing |
| `std::process::Command::env` | 1 | 1 | `crates/zed-native/src/link.rs:97` | missing |
| `std::process::Command::env_remove` | 1 | 1 | `crates/zed-native/src/link.rs:98` | missing |
| `std::process::Command::new` | 1 | 1 | `crates/zed-native/src/link.rs:94` | missing |
| `std::process::Command::output` | 2 | 1 | `crates/zed-native/src/link.rs:234` | missing |
| `std::process::ExitStatus::success` | 2 | 1 | `crates/zed-native/src/link.rs:239` | missing |
| `std::process::id` | 1 | 1 | `crates/zed-native/src/link.rs:558` | missing |
| `std::sync::lazy_lock::LazyLock<T, F>::new` | 2 | 1 | `crates/zed-kernel/src/types/rec.rs:90` | missing |
| `std::sync::once_lock::OnceLock<T>::get` | 15 | 5 | `crates/zed-kernel/src/types.rs:1734` | missing |
| `std::sync::once_lock::OnceLock<T>::get_or_init` | 12 | 8 | `crates/zed-kernel/src/types.rs:251` | missing |
| `std::sync::once_lock::OnceLock<T>::new` | 16 | 7 | `crates/zed-kernel/src/types.rs:539` | missing |
| `std::sync::once_lock::OnceLock<T>::set` | 10 | 5 | `crates/zed-kernel/src/types.rs:1773` | missing |
| `std::sync::once_lock::OnceLock<T>::take` | 4 | 3 | `crates/zed-kernel/src/types.rs:184` | row L6.13 |
| `std::sync::poison::PoisonError<T>::into_inner` | 1 | 1 | `crates/zedc-int/src/int.rs:347` | `x` |
| `std::sync::poison::mutex::<Mutex<T> as Default>::default` | 1 | 1 | `crates/zedc-stage/src/stage.rs:1995` | missing |
| `std::sync::poison::mutex::<MutexGuard<'_, T> as Deref>::deref` | 1 | 1 | `crates/zedc-int/src/int.rs:854` | `x` |
| `std::sync::poison::mutex::<MutexGuard<'_, T> as DerefMut>::deref_mut` | 4 | 3 | `crates/zed-kernel/src/types/bdd.rs:618` | `x` |
| `std::sync::poison::mutex::Mutex<T>::lock` | 13 | 4 | `crates/zed-kernel/src/types/bdd.rs:610` | missing |
| `std::sync::poison::mutex::Mutex<T>::new` | 1 | 1 | `crates/zed-kernel/src/types/bdd.rs:741` | missing |
| `std::thread::functions::spawn` | 4 | 2 | `crates/zed-kernel/src/types/bdd.rs:2417` | missing |
| `std::thread::local::LocalKey<Cell<T>>::get` | 8 | 4 | `crates/zed-kernel/src/num.rs:1495` | missing |
| `std::thread::local::LocalKey<Cell<T>>::replace` | 4 | 4 | `crates/zed-kernel/src/num.rs:1386` | row L6.13 |
| `std::thread::local::LocalKey<Cell<T>>::set` | 7 | 4 | `crates/zed-kernel/src/num.rs:1394` | missing |
| `std::thread::local::LocalKey<Cell<T>>::take` | 3 | 1 | `crates/zed-kernel/src/num.rs:1387` | row L6.13 |
| `std::thread::local::LocalKey<RefCell<T>>::replace` | 2 | 1 | `crates/zedc-base/src/work.rs:295` | missing |
| `std::thread::local::LocalKey<RefCell<T>>::set` | 1 | 1 | `crates/zedc-types/src/ty.rs:4073` | missing |
| `std::thread::local::LocalKey<RefCell<T>>::take` | 1 | 1 | `crates/zedc-types/src/ty.rs:4078` | row L6.13 |
| `std::thread::local::LocalKey<RefCell<T>>::with_borrow` | 1 | 1 | `crates/zed-kernel/src/types.rs:1771` | missing |
| `std::thread::local::LocalKey<RefCell<T>>::with_borrow_mut` | 16 | 4 | `crates/zed-kernel/src/types.rs:250` | missing |
| `std::thread::local::LocalKey<T>::try_with` | 8 | 4 | `crates/zed-kernel/src/deep.rs:30` | missing |
| `std::thread::local::LocalKey<T>::with` | 47 | 9 | `crates/zed-kernel/src/types.rs:348` | missing |
| `std::thread::local::thread_local!` | 25 | 14 | `crates/zed-kernel/src/num.rs:1357` | missing |
| `unicode_ident::is_xid_continue` | 13 | 4 | `crates/zedc-syntax/src/lex/name.rs:16` | row S.1c |
| `unicode_ident::is_xid_start` | 5 | 3 | `crates/zedc-syntax/src/lex/name.rs:16` | row S.1c |
| `unicode_normalization::<&'a str as UnicodeNormalization<Chars<'a>>>::nfc` | 1 | 1 | `crates/zedc-base/src/source.rs:126` | row S.1c |
| `unicode_normalization::lookups::canonical_combining_class` | 2 | 1 | `crates/zedc-base/src/source.rs:14` | row S.1c |
| `unicode_normalization::quick_check::is_nfc` | 4 | 1 | `crates/zedc-base/src/source.rs:15` | row S.1c |
| `unicode_script::<ScriptExtension as From<Script>>::from` | 1 | 1 | `crates/zedc-syntax/src/lex/name.rs:65` | row S.1c |
| `unicode_script::<char as UnicodeScript>::script` | 1 | 1 | `crates/zedc-syntax/src/lex/name.rs:78` | row S.1c |
| `unicode_script::<char as UnicodeScript>::script_extension` | 1 | 1 | `crates/zedc-syntax/src/lex/name.rs:69` | row S.1c |
| `unicode_script::Script::full_name` | 1 | 1 | `crates/zedc-syntax/src/lex/name.rs:84` | row S.1c |
| `unicode_script::ScriptExtension::for_str` | 1 | 1 | `crates/zedc-syntax/src/lex/name.rs:59` | row S.1c |
| `unicode_script::ScriptExtension::intersection` | 1 | 1 | `crates/zedc-syntax/src/lex/name.rs:69` | row S.1c |
| `unicode_script::ScriptExtension::is_empty` | 2 | 1 | `crates/zedc-syntax/src/lex/name.rs:59` | row S.1c |
| `unicode_script::ScriptExtension::union` | 1 | 1 | `crates/zedc-syntax/src/lex/name.rs:66` | row S.1c |
