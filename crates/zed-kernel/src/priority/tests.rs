use super::*;

/// A fixed draw of the degree `q.len() - 1` (4 or 7), so that the tests do not depend on the
/// system's random bytes.
fn fixed(q: &[u64], r: u64) -> Priorities {
    let p = match q.len() {
        5 => Priorities::new(0),
        8 => Priorities::eight_wise(0),
        n => panic!("no degree {}", n - 1),
    };
    let mut all = [0; 8];
    all[..q.len()].copy_from_slice(q);
    let degree = q.len() - 1;
    p.draw
        .set(Draw { q: all, degree, r })
        .expect("a new use has no draw");
    p
}

/// `P` is prime, so `0..P` is a field and the values of `q` at distinct points are independent
/// (module comment), and it is the largest prime below `2^64`, as its doc says. Red when `P` is
/// changed to `2^64 - 57` (composite) or to `2^64 - 83` (a smaller prime): checked 2026-11-19.
#[test]
fn p_is_the_largest_prime_below_2_to_the_64() {
    assert!(zed_numtheory::is_prime(P));
    for n in P + 1..=u64::MAX {
        assert!(!zed_numtheory::is_prime(n), "{n} is prime");
    }
}

#[test]
fn the_field_operations_agree_with_division_by_p() {
    let p = u128::from(P);
    // P - 60 times P - 1 or P - 2 makes the second fold of the product carry
    // past 2^64: a reduction that folds the high word twice in 64-bit
    // arithmetic and drops that carry gives a wrong product there, and on no
    // other pair of this test (found by the cross-review XR-xor-shape-round-7-high).
    let edges = [
        0,
        1,
        2,
        58,
        59,
        60,
        P - 60,
        P - 2,
        P - 1,
        1 << 32,
        (1 << 63) + 5,
    ];
    let mut rng = crate::seed::Rng::new(1);
    let mut values: Vec<u64> = edges.to_vec();
    for _ in 0..2000 {
        values.push(rng.below_u64(P));
    }
    for &a in &values {
        for &b in &values[..40] {
            assert_eq!(
                u128::from(mul(a, b)),
                u128::from(a) * u128::from(b) % p,
                "{a} * {b}"
            );
            assert_eq!(
                u128::from(add(a, b)),
                (u128::from(a) + u128::from(b)) % p,
                "{a} + {b}"
            );
        }
    }
}

#[test]
fn a_priority_is_the_polynomial_at_the_key() {
    let fours: &[u64] = &[3, P - 1, 0, 1 << 40, 7];
    let sevens: &[u64] = &[3, P - 1, 0, 1 << 40, 7, P - 59 - 1, 1, 1 << 63];
    for q in [fours, sevens] {
        let pr = fixed(q, 5);
        for x in [0, 1, 2, 1000, u64::MAX, P, P + 3] {
            let x_mod = u128::from(x % P);
            let p = u128::from(P);
            let want = q
                .iter()
                .fold(0u128, |acc, &c| (acc * x_mod + u128::from(c)) % p);
            assert_eq!(u128::from(pr.of(x)), want, "degree {}, {x}", q.len() - 1);
        }
        // The numbers from `P` up share the points of `0` to `58`.
        assert_eq!(pr.of(P + 3), pr.of(3));
    }
}

#[test]
fn a_draw_of_degree_4_is_the_first_five_coefficients_of_one_of_degree_7() {
    // Under one seed the two degrees draw the same leading coefficients, in the same order,
    // so a seed's degree-4 priorities did not change when degree 7 was added; and the two
    // degrees give different priorities, the higher terms being drawn.
    // The words include P and u64::MAX, which are drawn again.
    let words = || {
        let mut i = 0u64;
        move || {
            i += 1;
            match i {
                2 => P,
                5 => u64::MAX,
                _ => i.wrapping_mul(0x9e37_79b9_7f4a_7c15) % P,
            }
        }
    };
    let four = draw_from(words(), 4);
    let seven = draw_from(words(), 7);
    assert_eq!((four.degree, seven.degree), (4, 7));
    assert_eq!(four.q[..5], seven.q[..5]);
    assert!(four.q[5..].iter().all(|&c| c == 0));
    assert!(seven.q.iter().chain([&four.r, &seven.r]).all(|&c| c < P));
    // r follows the coefficients: the sixth word kept in degree 4, the ninth in degree 7.
    assert_eq!(four.r, seven.q[5]);
    assert_ne!(four.at(12345), seven.at(12345));
}

/// `g` of `bytes` written in pieces of the sizes `cuts`, taken in turn.
fn g_of(r: u64, bytes: &[u8], cuts: &[usize]) -> u64 {
    let mut s = Stream {
        r,
        acc: 1,
        pending: 0,
        filled: 0,
        len: 0,
    };
    let mut rest = bytes;
    for &c in cuts.iter().cycle() {
        if rest.is_empty() {
            break;
        }
        let c = c.min(rest.len());
        std::hash::Hasher::write(&mut s, &rest[..c]);
        rest = &rest[c..];
    }
    s.end()
}

#[test]
fn the_hash_of_a_stream_is_its_polynomial_however_it_is_written() {
    let r = 0x1234_5678_9abc_def1;
    let bytes: Vec<u8> = (0..23u8)
        .map(|i| i.wrapping_mul(37).wrapping_add(11))
        .collect();
    // The polynomial written out: a leading 1, the words, the last padded with zeros, then the
    // length. No word here is `P - 1` or more, so each is one symbol.
    let mut words: Vec<u64> = bytes
        .chunks(8)
        .map(|c| {
            let mut w = [0; 8];
            w[..c.len()].copy_from_slice(c);
            u64::from_le_bytes(w)
        })
        .collect();
    words.push(bytes.len() as u64);
    assert!(words.iter().all(|&w| w < P - 1));
    let want = words.iter().fold(1, |acc, &a| add(mul(acc, r), a));
    for cuts in [&[23][..], &[1], &[3, 5], &[2, 7, 1], &[8], &[9, 16]] {
        assert_eq!(g_of(r, &bytes, cuts), want, "{cuts:?}");
    }
}

#[test]
fn streams_that_differ_only_in_length_or_trailing_zeros_hash_apart() {
    // The leading 1 keeps a stream from equaling the same stream after zero words, and the
    // length keeps a stream from equaling it with zero bytes added to its last word.
    let r = 0x0fed_cba9_8765_4321;
    let streams: [&[u8]; 6] = [&[], &[0], &[0; 8], &[0; 9], &[7], &[7, 0]];
    for (i, a) in streams.iter().enumerate() {
        for b in &streams[i + 1..] {
            assert_ne!(g_of(r, a, &[3]), g_of(r, b, &[3]), "{a:?} {b:?}");
        }
    }
}

#[test]
fn a_word_of_p_minus_1_or_more_is_two_symbols_no_other_word_begins_with() {
    let r = 0x2468_ace0_1357_9bdf;
    let symbols = |ss: &[u64]| ss.iter().fold(1, |acc, &s| add(mul(acc, r), s));
    let le = |ws: &[u64]| ws.iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<u8>>();
    // `P - 1`, `P` and `u64::MAX` are the escape and then their excess over `P - 1`.
    for (w, rest) in [(P - 1, 0), (P, 1), (u64::MAX, 59)] {
        assert_eq!(
            g_of(r, &le(&[w]), &[8]),
            symbols(&[P - 1, rest, 8]),
            "{w:#x}"
        );
    }
    // Words of one symbol below the escape, for comparison.
    assert_eq!(g_of(r, &le(&[P - 2]), &[8]), symbols(&[P - 2, 8]));
    // The word `P` and the two words `P - 1`, `1` are distinct streams with distinct symbols:
    // the escape is never read as a word of its own.
    let one = le(&[P]);
    let two = le(&[P - 1, 1]);
    assert_ne!(g_of(r, &one, &[3]), g_of(r, &two, &[3]));
}

#[test]
fn equal_keys_take_equal_priorities_whatever_the_draw() {
    // Every draw, the run's included: a priority is a function of the key.
    let drawn = Priorities::new(1);
    let a = fixed(&[1, 2, 3, 4, 5], 6);
    let b = fixed(&[5, 4, 3, 2, 1, 9, 8, 7], 7);
    let key = (17u64, "a name", -5i64);
    let other = (17u64, "a name", -6i64);
    for p in [&drawn, &a, &b] {
        assert_eq!(p.hash(&key), p.hash(&key.clone()));
        assert_eq!(p.of(99), p.of(99));
    }
    // Two fixed draws, checked once: the keys and the draws are told apart.
    assert_ne!(a.hash(&key), b.hash(&key));
    assert_ne!(a.hash(&key), a.hash(&other));
}

/// The fingerprint primes of seeds 0 to 255 are in their ranges, `P1` prime and `P2 = 2Q + 1`
/// with `Q` and `P2` prime, and the draws they took are printed: the observed rates stated at
/// `fingerprint_primes` (against about 41.9 draws per prime for `P1`, and about 1310 per safe
/// prime for `Q` from the Hardy-Littlewood conjecture), and the time of one draw of both.
#[test]
fn fingerprint_primes_draw_rates() {
    let seeds = 256u64;
    let (mut sum, mut most) = ([0u64; 2], [0u64; 2]);
    let start = std::time::Instant::now();
    for seed in 0..seeds {
        let ([p1, p2], draws) =
            fingerprint_primes_from(seeded_words(seed, 21), seeded_words(seed, 22));
        assert!(
            (1 << 60..1 << 61).contains(&p1) && zed_numtheory::is_prime(p1),
            "P1 {p1}"
        );
        let q = (p2 - 1) / 2;
        assert!((1 << 59..1 << 60).contains(&q), "Q {q}");
        assert!(
            zed_numtheory::is_prime(q) && zed_numtheory::is_prime(p2),
            "P2 {p2}"
        );
        for i in 0..2 {
            sum[i] += draws[i];
            most[i] = most[i].max(draws[i]);
        }
    }
    let per = start.elapsed() / u32::try_from(seeds).expect("a few seeds");
    let mean = sum.map(|s| s as f64 / seeds as f64);
    println!(
        "fingerprint primes over {seeds} seeds: P1 {:.1} draws per prime (most {}), Q {:.0} draws \
         per safe prime (most {}); {per:?} per draw of both",
        mean[0], most[0], mean[1], most[1]
    );
    // A draw that took one candidate each time would mean the test of primality accepts all.
    assert!(mean[0] > 10.0 && mean[1] > 100.0, "{mean:?}");
}
