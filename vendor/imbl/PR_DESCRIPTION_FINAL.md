# HAMT with SIMD (swiss table like)

## Summary

PR changes small and non-small nodes to hold partial hashes (u8x16) that can be quickly used to find items. This allows:
- Small nodes to grow up to 100% occupancy
- Non-small nodes to grow until one group overflows
- Creates very dense tries

## Benchmark Highlights

- 58 total benchmarks
- 42 benchmarks (72%) showed improvements
- 11 benchmarks (19%) showed regressions
- 5 benchmarks (9%) remained neutral

| Benchmark | Baseline | New | Change |
|-----------|----------|-----|--------|
| hashmap_i64/insert_100 | 36.32 µs | 37.31 µs | +2.7% |
| hashmap_i64/insert_1000 | 680.60 µs | 632.24 µs | **-7.1%** |
| hashmap_i64/insert_10000 | 10.25 ms | 10.17 ms | -0.8% |
| hashmap_i64/insert_50000 | 64.11 ms | 64.21 ms | +0.2% |
| hashmap_i64/insert_mut_100 | 4.92 µs | 4.25 µs | **-13.6%** |
| hashmap_i64/insert_mut_1000 | 71.50 µs | 58.50 µs | **-18.2%** |
| hashmap_i64/insert_mut_5000 | 276.75 µs | 238.43 µs | **-13.8%** |
| hashmap_i64/insert_mut_10000 | 628.02 µs | 406.68 µs | **-35.2%** |
| hashmap_i64/insert_mut_50000 | 4.20 ms | 3.84 ms | **-8.6%** |
| hashmap_i64/insert_mut_100000 | 8.22 ms | 7.24 ms | **-11.9%** |
| hashmap_i64/iter_1000 | 6.95 µs | 6.48 µs | **-6.8%** |
| hashmap_i64/iter_10000 | 56.16 µs | 58.17 µs | +3.6% |
| hashmap_i64/iter_100000 | 1.48 ms | 1.25 ms | **-15.5%** |
| hashmap_i64/lookup_100 | 1.32 µs | 1.38 µs | +4.5% |
| hashmap_i64/lookup_1000 | 16.95 µs | 14.49 µs | **-14.5%** |
| hashmap_i64/lookup_5000 | 93.02 µs | 79.98 µs | **-14.0%** |
| hashmap_i64/lookup_10000 | 204.87 µs | 169.65 µs | **-17.2%** |
| hashmap_i64/lookup_50000 | 1.62 ms | 1.62 ms | 0.0% |
| hashmap_i64/lookup_100000 | 3.25 ms | 3.29 ms | +1.2% |
| hashmap_i64/lookup_500000 | 58.68 ms | 24.94 ms | **-57.5%** |
| hashmap_i64/lookup_ne_10000 | 215.75 µs | 143.57 µs | **-33.5%** |
| hashmap_i64/lookup_ne_100000 | 3.42 ms | 2.86 ms | **-16.4%** |
| hashmap_i64/remove_100 | 33.34 µs | 34.39 µs | +3.1% |
| hashmap_i64/remove_1000 | 675.75 µs | 671.72 µs | -0.6% |
| hashmap_i64/remove_10000 | 10.31 ms | 10.33 ms | +0.2% |
| hashmap_i64/remove_50000 | 64.78 ms | 66.75 ms | +3.0% |
| hashmap_i64/remove_mut_100 | 5.26 µs | 4.41 µs | **-16.2%** |
| hashmap_i64/remove_mut_1000 | 63.75 µs | 51.62 µs | **-19.0%** |
| hashmap_i64/remove_mut_10000 | 645.17 µs | 484.52 µs | **-24.9%** |
| hashmap_str/insert_100 | 63.60 µs | 62.45 µs | -1.8% |
| hashmap_str/insert_1000 | 977.86 µs | 1042.10 µs | **+6.6%** |
| hashmap_str/insert_10000 | 12.92 ms | 12.83 ms | -0.7% |
| hashmap_str/insert_50000 | 80.28 ms | 82.95 ms | +3.3% |
| hashmap_str/insert_mut_100 | 8.41 µs | 7.97 µs | **-5.2%** |
| hashmap_str/insert_mut_1000 | 116.37 µs | 104.64 µs | **-10.1%** |
| hashmap_str/insert_mut_5000 | 510.01 µs | 482.34 µs | **-5.4%** |
| hashmap_str/insert_mut_10000 | 1127.10 µs | 901.49 µs | **-20.0%** |
| hashmap_str/insert_mut_50000 | 6.68 ms | 6.58 ms | -1.5% |
| hashmap_str/insert_mut_100000 | 15.86 ms | 14.79 ms | **-6.7%** |
| hashmap_str/iter_1000 | 7.04 µs | 6.25 µs | **-11.2%** |
| hashmap_str/iter_10000 | 58.57 µs | 57.42 µs | -2.0% |
| hashmap_str/iter_100000 | 1.56 ms | 1.28 ms | **-17.9%** |
| hashmap_str/lookup_100 | 1.84 µs | 1.89 µs | +2.7% |
| hashmap_str/lookup_1000 | 21.93 µs | 21.99 µs | +0.3% |
| hashmap_str/lookup_5000 | 144.90 µs | 145.87 µs | +0.7% |
| hashmap_str/lookup_10000 | 486.16 µs | 418.74 µs | **-13.9%** |
| hashmap_str/lookup_50000 | 3.10 ms | 3.05 ms | -1.6% |
| hashmap_str/lookup_100000 | 6.80 ms | 6.51 ms | -4.3% |
| hashmap_str/lookup_500000 | 169.22 ms | 136.83 ms | **-19.1%** |
| hashmap_str/lookup_ne_10000 | 549.76 µs | 397.95 µs | **-27.6%** |
| hashmap_str/lookup_ne_100000 | 7.69 ms | 6.96 ms | **-9.5%** |
| hashmap_str/remove_100 | 62.93 µs | 61.80 µs | -1.8% |
| hashmap_str/remove_1000 | 949.88 µs | 966.02 µs | +1.7% |
| hashmap_str/remove_10000 | 13.01 ms | 12.78 ms | -1.8% |
| hashmap_str/remove_50000 | 80.64 ms | 79.35 ms | -1.6% |
| hashmap_str/remove_mut_100 | 7.67 µs | 7.10 µs | **-7.4%** |
| hashmap_str/remove_mut_1000 | 86.58 µs | 75.54 µs | **-12.7%** |
| hashmap_str/remove_mut_10000 | 1103.80 µs | 923.78 µs | **-16.3%** |

## Key Performance Observations

1. Bulk operations showed substantial improvements (avg. -13%, up to -35%)
2. Negative lookups improved by ~25% on average
3. Iteration showed ~10% average improvement on large collections
4. Regular lookups had mixed results depending on size, with exceptional gains on large collections (-57.5% for 500k)
5. Small maps (100 elements) showed minor regressions

The benchmarks are sensitive to various aspects and the denser trie might perform even better in practice.
