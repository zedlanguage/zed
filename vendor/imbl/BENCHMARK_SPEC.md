# Benchmark Specification - PR #131 Match

This document verifies that the benchmark file matches the PR #131 benchmark list exactly.

## Expected Benchmarks from PR #131

### hashmap_i64 (29 benchmarks)
1. insert_100
2. insert_1000
3. insert_10000
4. insert_50000
5. insert_mut_100
6. insert_mut_1000
7. insert_mut_5000
8. insert_mut_10000
9. insert_mut_50000
10. insert_mut_100000
11. iter_1000
12. iter_10000
13. iter_100000
14. lookup_100
15. lookup_1000
16. lookup_5000
17. lookup_10000
18. lookup_50000
19. lookup_100000
20. lookup_500000
21. lookup_ne_10000
22. lookup_ne_100000
23. remove_100
24. remove_1000
25. remove_10000
26. remove_50000
27. remove_mut_100
28. remove_mut_1000
29. remove_mut_10000

### hashmap_str (29 benchmarks)
1. insert_100
2. insert_1000
3. insert_10000
4. insert_50000
5. insert_mut_100
6. insert_mut_1000
7. insert_mut_5000
8. insert_mut_10000
9. insert_mut_50000
10. insert_mut_100000
11. iter_1000
12. iter_10000
13. iter_100000
14. lookup_100
15. lookup_1000
16. lookup_5000
17. lookup_10000
18. lookup_50000
19. lookup_100000
20. lookup_500000
21. lookup_ne_10000
22. lookup_ne_100000
23. remove_100
24. remove_1000
25. remove_10000
26. remove_50000
27. remove_mut_100
28. remove_mut_1000
29. remove_mut_10000

## Total: 58 benchmarks (29 i64 + 29 str)

## Current Implementation in benches/hashmap.rs

### Lookup operations
- Sizes: [100, 1000, 5000, 10000, 50000, 100000, 500000] ✅
- Count: 7 per type

### Lookup non-existent operations
- Sizes: [10000, 100000] ✅
- Count: 2 per type

### Insert mutable operations
- Sizes: [100, 1000, 5000, 10000, 50000, 100000] ✅
- Count: 6 per type

### Remove mutable operations
- Sizes: [100, 1000, 10000] ✅
- Count: 3 per type

### Iteration operations
- Sizes: [1000, 10000, 100000] ✅
- Count: 3 per type

### Immutable insert operations
- Sizes: [100, 1000, 10000, 50000] ✅
- Count: 4 per type

### Immutable remove operations
- Sizes: [100, 1000, 10000, 50000] ✅
- Count: 4 per type

## Verification

Total benchmarks per type: 7 + 2 + 6 + 3 + 3 + 4 + 4 = **29 benchmarks** ✅

- hashmap_i64: 29 benchmarks ✅
- hashmap_str: 29 benchmarks ✅

**Grand Total: 58 benchmarks** ✅

## Status: EXACT MATCH ✅

The benchmark file now runs exactly the same benchmarks as listed in PR #131.
