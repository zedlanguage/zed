//! The inputs of the benchmarks in `bench.rs`, which hold each reference program to its order in
//! the input's size (TEST-bench-move-rest, P170). Here each reference program runs without error
//! on each input at small sizes, and reference 14 prints what its O(n²) form prints on each of
//! the clustering inputs.

use std::fmt::Write;
use std::fs;

/// A benchmark of reference `number` on `input`, at size `n` and power `power`.
pub(super) struct Input {
    pub(super) what: &'static str,
    pub(super) number: &'static str,
    pub(super) n: usize,
    pub(super) power: u32,
    pub(super) input: fn(usize) -> String,
}

/// A line per `i` in `0..n`.
fn lines(n: usize, line: impl Fn(usize) -> String) -> String {
    (0..n).fold(String::new(), |mut s, i| {
        writeln!(s, "{}", line(i)).expect("writing to a String");
        s
    })
}

/// Runs reference `number` on `text`, written to a file named by `what` and `m`; it must not
/// fail.
pub(super) fn runs(what: &str, number: &str, m: usize, text: &str) {
    let path = input_path(what, m);
    fs::write(&path, text).expect("writing an input");
    let (_, result) = zed_corpus_ref::run(number, &path);
    fs::remove_file(&path).expect("removing an input");
    assert_eq!(result, Ok(()), "{what} at {m}");
}

/// The file the input of `what` at size `m` is written to.
pub(super) fn input_path(what: &str, m: usize) -> String {
    let name = what.replace(' ', "_");
    format!("{}/build/ref_{name}_{m}.in", zed_tools::impl_root())
}

pub(super) const WORD_COUNT: Input = Input {
    what: "word count",
    number: "01",
    n: 4000,
    power: 1,
    input: |n| lines(n, |i| format!("the w{i} Cat")),
};

/// One word as long as the input: a line of the output per length up to it.
pub(super) const HISTOGRAM: Input = Input {
    what: "histogram",
    number: "02",
    n: 20000,
    power: 1,
    input: |n| format!("{} {}\n", "x".repeat(n), "a bb ".repeat(n / 5)),
};

/// The table of an edit distance has a cell per pair of characters.
pub(super) const EDIT_DISTANCE: Input = Input {
    what: "edit distance",
    number: "03",
    n: 300,
    power: 2,
    input: |n| format!("{} {}\n", "ab".repeat(n / 2), "ba".repeat(n / 2)),
};

pub(super) const RUNNING_VARIANCE: Input = Input {
    what: "running variance",
    number: "04",
    n: 3000,
    power: 1,
    input: |n| lines(n, |i| format!("{}.5e{}", i % 97, i as i64 % 40 - 20)),
};

pub(super) const MAX_PREFIX_SUM: Input = Input {
    what: "max prefix sum",
    number: "05",
    n: 8000,
    power: 1,
    input: |n| lines(n, |i| format!("{}", (i as i64 * 7919) % 2001 - 1000)),
};

/// A k by k product has k³ terms.
pub(super) const MATRIX_MULTIPLY: Input = Input {
    what: "matrix multiply",
    number: "06",
    n: 12,
    power: 3,
    input: |k| {
        let cells: Vec<String> = (0..k).map(|j| format!("{}.5", j % 7)).collect();
        let row = cells.join(" ") + "\n";
        format!("{k} {k} {k}\n{}", row.repeat(2 * k))
    },
};

pub(super) const JSON_DEPTH: Input = Input {
    what: "json depth",
    number: "07",
    n: 20000,
    power: 1,
    input: |n| format!("{}1{}\n", "[".repeat(n), "]".repeat(n)),
};

pub(super) const JSON_OBJECT_DEPTH: Input = Input {
    what: "json object depth",
    number: "07",
    n: 20000,
    power: 1,
    input: |n| format!("{}1{}\n", "{\"a\": ".repeat(n), "}".repeat(n)),
};

pub(super) const JSON_WIDTH: Input = Input {
    what: "json width",
    number: "07",
    n: 20000,
    power: 1,
    input: |n| format!("[{}true]\n", "\"a b\" , ".repeat(n)),
};

pub(super) const JSON_FAILURE: Input = Input {
    what: "json failure",
    number: "07",
    n: 20000,
    power: 1,
    input: |n| format!("{}1,\n", "[".repeat(n)),
};

pub(super) const PERCENT_DECODING: Input = Input {
    what: "percent decoding",
    number: "08",
    n: 10000,
    power: 1,
    input: |n| format!("{}\n", "caf%C3%A9%20".repeat(n / 12)),
};

pub(super) const CANONICAL_EQUALITY: Input = Input {
    what: "canonical equality",
    number: "09",
    n: 5000,
    power: 1,
    input: |n| lines(n, |i| format!("New-York {i} | new york {i}")),
};

pub(super) const REGEX_LINES: Input = Input {
    what: "regex lines",
    number: "10",
    n: 3000,
    power: 1,
    input: |n| lines(n, |i| format!("{:02}:{:02}", i % 30, i % 70)),
};

pub(super) const REGEX_LENGTH: Input = Input {
    what: "regex length",
    number: "10",
    n: 3000,
    power: 1,
    input: |n| format!("{}\n", "2".repeat(n)),
};

pub(super) const CSV: Input = Input {
    what: "csv",
    number: "11",
    n: 20000,
    power: 1,
    input: |n| format!("{}\n", "\"x,y\",z,".repeat(n / 8)),
};

/// The corpus program fills a CYK table; the reference prints the same answer from one pass.
pub(super) const BALANCED_BRACKETS: Input = Input {
    what: "balanced brackets",
    number: "12",
    n: 20000,
    power: 1,
    input: |n| format!("{}\n", "()".repeat(n / 2)),
};

pub(super) const DEEP_BRACKETS: Input = Input {
    what: "deep brackets",
    number: "12",
    n: 20000,
    power: 1,
    input: |n| format!("{}{}\n", "(".repeat(n / 2), ")".repeat(n / 2)),
};

pub(super) const UNION_FIND: Input = Input {
    what: "union find",
    number: "13",
    n: 4000,
    power: 1,
    input: |n| lines(n, |i| format!("{} {}", i, i + 1)) + &lines(n, |i| format!("? 0 {i}")),
};

/// The gap between node numbers of `UNION_FIND_HUGE_NUMBERS`.
const STEP: usize = 10_000_000_000_000;

/// Memory and time follow the edges and queries, not the node numbers, which here are about
/// 10^13 times the input's length.
pub(super) const UNION_FIND_HUGE_NUMBERS: Input = Input {
    what: "union find huge numbers",
    number: "13",
    n: 4000,
    power: 1,
    input: |n| {
        lines(n, |i| format!("{} {}", i * STEP, (i + 1) * STEP))
            + &lines(n, |i| format!("? 0 {}", i * STEP))
    },
};

/// A clustering input for reference 14 at size `n`: its output at `n` is checked to be that of
/// the O(n²) form before it is timed. The merges follow a Delaunay triangulation: O(n log n).
const fn clustering(what: &'static str, input: fn(usize) -> String) -> Input {
    Input {
        what,
        number: "14",
        n: 1000,
        power: 1,
        input,
    }
}

/// The side of the smallest square grid of at least `n` points.
fn side(n: usize) -> usize {
    (1..).find(|w| w * w >= n).expect("a side")
}

/// Nearly collinear points far apart.
pub(super) const CLUSTERING_NEAR_A_LINE: Input = clustering("clustering near a line", |n| {
    format!("1\n{}", lines(n, |i| format!("{} {}", i * i, i % 3)))
});

/// A grid: every side of every square at one distance, so the label rule orders whole levels.
pub(super) const CLUSTERING_GRID: Input = clustering("clustering grid", |n| {
    let w = side(n);
    format!(
        "{}\n{}",
        n / 2,
        lines(n, |i| format!("{} {}", i % w, i / w))
    )
});

/// The grid turned by the angle whose cosine is 3/5 and scaled by 5: (3a + 4b, -4a + 3b).
pub(super) const CLUSTERING_ROTATED_GRID: Input = clustering("clustering rotated grid", |n| {
    let w = side(n);
    let point = |i: usize| {
        let (a, b) = ((i % w) as i64, (i / w) as i64);
        format!("{} {}", 3 * a + 4 * b, -4 * a + 3 * b)
    };
    format!("{}\n{}", n / 2, lines(n, point))
});

/// splitmix64 of `i`, cut to 30 bits.
fn hash(i: usize) -> u64 {
    let mut z = (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    (z ^ (z >> 31)) >> 34
}

/// The size of the random clustering inputs (their O(n²) check stays at 1000 points). Their cost is mostly the sorts and the
/// triangulation, n log n with little linear work beside it, and a sort's comparisons,
/// n log₂ n - 1.44 n, grow 10.8 times from 1000 to 8000 points but 10.3 times from 4000 to 32000:
/// at 1000 the ratio sat at 10.49 of the 10.5 allowed, and a cheaper reading of the numbers
/// (FAIL-ref-text-reading) pushed it over, though every size got faster.
const RANDOM_N: usize = 4000;

/// Points in random places: each coordinate a hash of its position in the input.
pub(super) const CLUSTERING_RANDOM: Input = Input {
    n: RANDOM_N,
    ..clustering("clustering random", |n| {
        format!(
            "1\n{}",
            lines(n, |i| format!("{} {}", hash(2 * i + 1), hash(2 * i + 2)))
        )
    })
};

/// Point i is (i mod 3, i mod 2), which fixes i mod 6: six distinct points, each about n/6 times
/// in turn, so all but six points equal an earlier one. Three clusters: the merges join every
/// set of equal points at distance 0, then stop after three of the seven pairs at distance 1.
pub(super) const CLUSTERING_EQUAL_POINTS: Input = clustering("clustering equal points", |n| {
    format!("3\n{}", lines(n, |i| format!("{} {}", i % 3, i % 2)))
});

/// Points all on one line, in an order far from sorted: the triangulation is their path.
pub(super) const CLUSTERING_ON_A_LINE: Input = clustering("clustering on a line", |n| {
    let point = |i: usize| {
        let x = i * 7919 % n;
        format!("{x} {}", 2 * x)
    };
    format!("1\n{}", lines(n, point))
});

/// The 8192 lattice points of x² + y² = 5 · 13 · 17 · 29 · 37 · 41 · 53 · 61 · 73 · 89 · 97, each
/// a product of one of a ± bi per prime p = a² + b², times a unit.
fn circle() -> Vec<(i64, i64)> {
    let primes = [
        (1, 2),
        (2, 3),
        (1, 4),
        (2, 5),
        (1, 6),
        (4, 5),
        (2, 7),
        (5, 6),
        (3, 8),
        (5, 8),
        (4, 9),
    ];
    let mut zs: Vec<(i64, i64)> = vec![(1, 0)];
    for (a, b) in primes {
        zs = zs
            .iter()
            .flat_map(|&(x, y)| {
                [
                    (x * a - y * b, x * b + y * a),
                    (x * a + y * b, y * a - x * b),
                ]
            })
            .collect();
    }
    zs.into_iter()
        .flat_map(|(x, y)| [(x, y), (-y, x), (-x, -y), (y, -x)])
        .collect()
}

/// Points all on one circle, where every in-circle test of four of them is 0: the first n of the
/// lattice points of `circle`.
pub(super) const CLUSTERING_CIRCLE: Input = clustering("clustering circle", |n| {
    let (x, y): (Vec<i64>, Vec<i64>) = circle()[..n].iter().copied().unzip();
    format!("1\n{}", lines(n, |i| format!("{} {}", x[i], y[i])))
});

/// Two parabolas facing apart, x = ±(10000 + t²) and y = 5000t: every point is on the hull of its
/// half, so each merge of the triangulation walks long hull chains.
pub(super) const CLUSTERING_TWO_PARABOLAS: Input = clustering("clustering two parabolas", |n| {
    format!(
        "1\n{}",
        lines(n, |i| {
            let t = (i / 2) as i64 - n as i64 / 4;
            let x = 10_000 + t * t;
            let x = if i % 2 == 0 { -x } else { x };
            format!("{x} {}", 5_000 * t)
        })
    )
});

/// A coordinate of `chunks` blocks of nine decimal digits, block j the hash of `(seed, j)`: the
/// first blocks do not depend on `chunks`, so with more blocks the points scale up by a power of
/// 10 and move by less than one unit of the shorter ones.
fn wide(seed: usize, chunks: usize) -> String {
    (0..chunks).fold(String::new(), |mut s, j| {
        let block = hash(seed * 64 + j);
        if j == 0 {
            write!(s, "{}", block % 900_000_000 + 100_000_000)
        } else {
            write!(s, "{:09}", block % 1_000_000_000)
        }
        .expect("writing to a String");
        s
    })
}

/// `n` random points whose coordinates have `chunks` blocks of nine digits.
pub(super) fn wide_random_points(n: usize, chunks: usize) -> String {
    let point = |i: usize| format!("{} {}", wide(2 * i + 1, chunks), wide(2 * i + 2, chunks));
    format!("1\n{}", lines(n, point))
}

/// Random points with coordinates of 72 digits (240 bits): every product and sum in the
/// predicates is several 64-bit words long, and the in-circle determinant up to 4b + 8 = 968 bits
/// (COMPLEXITY F39). At a fixed coordinate size the bound O(L + n log n · M(b)) is O(n log n).
/// At [`RANDOM_N`] points.
pub(super) const CLUSTERING_RANDOM_WIDE: Input = Input {
    n: RANDOM_N,
    ..clustering("clustering random wide", |n| wide_random_points(n, 8))
};

/// Every edit prints every cell, so the output is quadratic.
pub(super) const SPREADSHEET: Input = Input {
    what: "spreadsheet",
    number: "15",
    n: 200,
    power: 2,
    input: |n| {
        lines(n, |i| match i {
            0 => "c0 = 1".to_string(),
            _ => format!("c{i} = c{}+1", i - 1),
        })
    },
};

/// A formula is read once, so n edits of a cell it does not name cost nothing for its n terms.
pub(super) const SPREADSHEET_LONG_FORMULA: Input = Input {
    what: "spreadsheet long formula",
    number: "15",
    n: 4000,
    power: 1,
    input: |n| {
        let edits = lines(n, |i| format!("b = {i}"));
        format!("a = {}\n{edits}", vec!["1"; n].join("+"))
    },
};

/// A formula keeps each name once with its multiplicity, so its n terms are one dependency edge.
pub(super) const SPREADSHEET_REPEATED_TERM: Input = Input {
    what: "spreadsheet repeated term",
    number: "15",
    n: 4000,
    power: 1,
    input: |n| {
        let edits = lines(n, |i| format!("b = {i}"));
        format!("a = {}\n{edits}", vec!["b"; n].join("+"))
    },
};

pub(super) const GAME_PLAYERS: Input = Input {
    what: "game players",
    number: "16",
    n: 10000,
    power: 1,
    input: |n| lines(n, |i| format!("0 p{i} 3")),
};

pub(super) const GAME_TICKS: Input = Input {
    what: "game ticks",
    number: "16",
    n: 10000,
    power: 1,
    input: |n| lines(n, |i| format!("{i} ann 1")),
};

pub(super) const SENSOR_PIPELINE: Input = Input {
    what: "sensor pipeline",
    number: "17",
    n: 10000,
    power: 1,
    input: |n| lines(n, |i| format!("{i} temp {}", i % 30)),
};

pub(super) const WORD_FREQUENCY: Input = Input {
    what: "word frequency",
    number: "18",
    n: 10000,
    power: 1,
    input: |n| lines(n, |i| format!("{i} w{} Hello", i % 1000)),
};

pub(super) const BANK_LEDGER: Input = Input {
    what: "bank ledger",
    number: "19",
    n: 5000,
    power: 1,
    input: |n| lines(n, |i| format!("open a{i}")) + &lines(n, |i| format!("dep a{i} {i}")),
};

pub(super) const TAINT: Input = Input {
    what: "taint",
    number: "20",
    n: 10000,
    power: 1,
    input: |n| lines(n, |_| "<b>fish & chips</b>".to_string()),
};

pub(super) const STATS: Input = Input {
    what: "stats",
    number: "21",
    n: 5000,
    power: 1,
    input: |n| lines(n, |i| format!("{}.5 {}", i % 100, i % 7)),
};

pub(super) const TOP_K: Input = Input {
    what: "top k",
    number: "22",
    n: 10000,
    power: 1,
    input: |n| lines(n, |i| format!("p{i} {}", (i * 7919) % 1009)),
};

pub(super) const JOIN_ZOO: Input = Input {
    what: "join zoo",
    number: "23",
    n: 5000,
    power: 1,
    input: |n| lines(n, |i| format!("O {i} {i}")) + &lines(n, |i| format!("P {} 1", 2 * i)),
};

pub(super) const WEIGHTED_PICK: Input = Input {
    what: "weighted pick",
    number: "24",
    n: 5000,
    power: 1,
    input: |n| {
        let weights: Vec<String> = (0..n).map(|i| (i % 5).to_string()).collect();
        weights.join(" ") + "\n" + &lines(n, |i| i.to_string())
    },
};

pub(super) const AUTOCORRELATION: Input = Input {
    what: "autocorrelation",
    number: "25",
    n: 8000,
    power: 1,
    input: |n| {
        let xs: Vec<String> = (0..n).map(|i| (i % 19).to_string()).collect();
        xs.join(" ") + "\n"
    },
};

/// The number of steps is a value in the input, not a length; this is the length.
pub(super) const HEAT_STENCIL: Input = Input {
    what: "heat stencil",
    number: "26",
    n: 5000,
    power: 1,
    input: |n| {
        let cells: Vec<String> = (0..n).map(|i| (i % 400).to_string()).collect();
        format!("3\n{}\n", cells.join(" "))
    },
};

pub(super) const PARENT_CHAIN: Input = Input {
    what: "parent chain",
    number: "27",
    n: 10000,
    power: 1,
    input: |n| format!("n0 -\n{}", lines(n, |i| format!("n{} n{i}", i + 1))),
};

pub(super) const PRECEDENCE_CLIMBING: Input = Input {
    what: "precedence climbing",
    number: "28",
    n: 10000,
    power: 1,
    input: |n| format!("{}1\n", "2 ^ 3 + ".repeat(n / 8)),
};

pub(super) const LATE_DEDUP: Input = Input {
    what: "late dedup",
    number: "29",
    n: 10000,
    power: 1,
    input: |n| lines(n, |i| format!("k{} {i} {i}", i % 100)),
};

pub(super) const CLIENT_SERVER: Input = Input {
    what: "client server",
    number: "30",
    n: 5000,
    power: 1,
    input: |n| lines(n, |i| format!("buy item{} {}", i % 50, i % 9)),
};

pub(super) const TYPECHECKER_CHAIN: Input = Input {
    what: "typechecker chain",
    number: "31",
    n: 5000,
    power: 1,
    input: |n| {
        lines(n, |i| match i {
            0 => "d0 = 1".to_string(),
            _ => format!("d{i} = d{} 1 +", i - 1),
        })
    },
};

/// Declared last to first, the order that takes the most rounds from all-unknown.
pub(super) const TYPECHECKER_BACKWARD: Input = Input {
    what: "typechecker backward",
    number: "31",
    n: 5000,
    power: 1,
    input: |n| {
        lines(n, |i| match n - 1 - i {
            0 => "d0 = 1".to_string(),
            k => format!("d{k} = d{} 1 +", k - 1),
        })
    },
};

pub(super) const TYPECHECKER_LENGTH: Input = Input {
    what: "typechecker length",
    number: "31",
    n: 20000,
    power: 1,
    input: |n| format!("x = 1{}\n", " 1 +".repeat(n / 4)),
};

pub(super) const TYPECHECKER_CYCLE: Input = Input {
    what: "typechecker cycle",
    number: "31",
    n: 5000,
    power: 1,
    input: |n| lines(n, |i| format!("d{i} = d{} 1 +", (i + 1) % n)),
};

/// The inputs whose reference is not 14.
const OTHERS: [Input; 42] = [
    WORD_COUNT,
    HISTOGRAM,
    EDIT_DISTANCE,
    RUNNING_VARIANCE,
    MAX_PREFIX_SUM,
    MATRIX_MULTIPLY,
    JSON_DEPTH,
    JSON_OBJECT_DEPTH,
    JSON_WIDTH,
    JSON_FAILURE,
    PERCENT_DECODING,
    CANONICAL_EQUALITY,
    REGEX_LINES,
    REGEX_LENGTH,
    CSV,
    BALANCED_BRACKETS,
    DEEP_BRACKETS,
    UNION_FIND,
    UNION_FIND_HUGE_NUMBERS,
    SPREADSHEET,
    SPREADSHEET_LONG_FORMULA,
    SPREADSHEET_REPEATED_TERM,
    GAME_PLAYERS,
    GAME_TICKS,
    SENSOR_PIPELINE,
    WORD_FREQUENCY,
    BANK_LEDGER,
    TAINT,
    STATS,
    TOP_K,
    JOIN_ZOO,
    WEIGHTED_PICK,
    AUTOCORRELATION,
    HEAT_STENCIL,
    PARENT_CHAIN,
    PRECEDENCE_CLIMBING,
    LATE_DEDUP,
    CLIENT_SERVER,
    TYPECHECKER_CHAIN,
    TYPECHECKER_BACKWARD,
    TYPECHECKER_LENGTH,
    TYPECHECKER_CYCLE,
];

/// The clustering inputs of reference 14.
const CLUSTERINGS: [Input; 9] = [
    CLUSTERING_NEAR_A_LINE,
    CLUSTERING_GRID,
    CLUSTERING_ROTATED_GRID,
    CLUSTERING_RANDOM,
    CLUSTERING_EQUAL_POINTS,
    CLUSTERING_ON_A_LINE,
    CLUSTERING_CIRCLE,
    CLUSTERING_TWO_PARABOLAS,
    CLUSTERING_RANDOM_WIDE,
];

/// Each reference program runs without error on each benchmark's input at small sizes.
#[test]
fn each_reference_runs_on_its_benchmark_inputs_at_small_sizes() {
    for input in &OTHERS {
        for m in [2, 9, 40] {
            runs(
                &format!("small {}", input.what),
                input.number,
                m,
                &(input.input)(m),
            );
        }
    }
}

/// On each clustering input at small sizes, reference 14 runs without error and prints what its
/// O(n²) form prints; so it does with coordinates of 9 to 72 digits.
#[test]
fn reference_14_agrees_with_its_quadratic_form_on_each_clustering_input_at_small_sizes() {
    for input in &CLUSTERINGS {
        for m in [2, 9, 40] {
            let text = (input.input)(m);
            let differs = super::clustering_differs_from_oracle(&text);
            assert!(
                differs.is_none(),
                "{}: the O(n²) form differs at {m}",
                input.what
            );
            runs(&format!("small {}", input.what), input.number, m, &text);
        }
    }
    for chunks in [1, 4, 8] {
        let text = wide_random_points(40, chunks);
        assert!(
            super::clustering_differs_from_oracle(&text).is_none(),
            "{chunks} blocks"
        );
    }
}
