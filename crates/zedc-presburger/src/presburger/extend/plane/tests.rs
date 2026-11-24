//! Tests of the integer hull (design B; META3 H1-H4): random rows against brute force, each
//! step's mutant caught, the corner hull against the O(beta) walk, the run against a literal
//! `<=` scan with every tree node counted, the dimension check, persistence and scaling.

use super::*;

fn row(a: i64, b: i64, c: i64) -> (Int, Int, Int) {
    (int(a), int(b), int(c))
}

/// xorshift64, so every run reads the same rows.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    /// Uniform in `-m..=m`.
    fn small(&mut self, m: i64) -> i64 {
        (self.next() % (2 * m as u64 + 1)) as i64 - m
    }
}

fn hull_of(rows: &[(Int, Int, Int)]) -> Option<Hull> {
    let mut h = Plane::all().hull;
    for (a, b, c) in rows {
        h = add(&h, a.clone(), b.clone(), c.clone())?;
    }
    Some(h)
}

fn holds_all(rows: &[(Int, Int, Int)], p: &P) -> bool {
    (rows.iter()).all(|(a, b, c)| &(a * &p.0) + &(b * &p.1) >= *c)
}

fn sides(t: &Tree) -> Vec<Row> {
    let mut v = vec![];
    to_vec(t, &mut v);
    v.into_iter().map(|s| (*s).clone()).collect()
}

/// Whether the integer point `p` is in `h`.
fn contains(h: &Hull, p: &P) -> bool {
    match h {
        Hull::Empty => false,
        Hull::Point(q) => q == p,
        Hull::Line { p0, d, lo, hi } => {
            let v = (&p.0 - &p0.0, &p.1 - &p0.1);
            if !cross(d, &v).is_zero() {
                return false;
            }
            // d is primitive, so v = t d for an integer t.
            let t = if d.0.is_zero() {
                v.1.div_floor(&d.1)
            } else {
                v.0.div_floor(&d.0)
            };
            lo.as_ref().is_none_or(|l| t >= *l) && hi.as_ref().is_none_or(|u| t <= *u)
        }
        Hull::Band { n, lo, hi } => {
            let f = dot(n, p);
            lo.as_ref().is_none_or(|l| f >= *l) && hi.as_ref().is_none_or(|u| f <= *u)
        }
        Hull::Poly { sides: t, .. } => sides(t).iter().all(|r| r.holds(p)),
    }
}

/// The invariants of a state: a Polygon's adjacent sides turn left, its vertices are integral,
/// no two sides are opposite, and a bounded one has three distinct vertices (positive area,
/// META3 H1); Lines and Bands have primitive directions and normals.
fn invariants(h: &Hull) -> Result<(), String> {
    match h {
        Hull::Poly { sides: t, bounded } => {
            let s = sides(t);
            let k = s.len();
            if k < 2 {
                return Err(format!("a Polygon of {k} sides"));
            }
            let pairs: Vec<(usize, usize)> = if *bounded {
                (0..k).map(|i| ((i + k - 1) % k, i)).collect()
            } else {
                (1..k).map(|i| (i - 1, i)).collect()
            };
            let mut vertices = vec![];
            for (i, j) in pairs {
                if !cross(&s[i].n(), &s[j].n()).is_positive() {
                    return Err(format!("sides {i}, {j} do not turn left: {s:?}"));
                }
                let q = meet(&s[i], &s[j]).ok_or("parallel sides")?;
                let p = integral(&q).ok_or_else(|| format!("vertex {q:?} not integral: {s:?}"))?;
                vertices.push(p);
            }
            // No redundant side (step 6): each side between two vertices has length. Bounded,
            // side i runs from vertex i to vertex i + 1; unbounded, the inner side j from
            // vertex j - 1 to vertex j, and the two end sides are rays.
            let n = vertices.len();
            let spans: Vec<(usize, usize)> = if *bounded {
                (0..k).map(|i| (i, (i + 1) % k)).collect()
            } else {
                (1..n).map(|j| (j - 1, j)).collect()
            };
            if let Some((i, _)) = spans.into_iter().find(|&(i, j)| vertices[i] == vertices[j]) {
                return Err(format!(
                    "a redundant side at vertex {:?}: {s:?}",
                    vertices[i]
                ));
            }
            for (i, r) in s.iter().enumerate() {
                if s[i + 1..].iter().any(|o| r.opposite(o)) {
                    return Err(format!("opposite sides, no area: {s:?}"));
                }
                if r.a.gcd(&r.b) != Int::ONE {
                    return Err(format!("side {r:?} not tightened"));
                }
            }
            vertices.sort();
            vertices.dedup();
            if *bounded && vertices.len() < 3 {
                return Err(format!("a bounded Polygon of {} vertices", vertices.len()));
            }
            Ok(())
        }
        Hull::Line { d, .. } if d.0.gcd(&d.1) != Int::ONE => Err("a Line not primitive".into()),
        Hull::Band { n, .. } if n.0.gcd(&n.1) != Int::ONE => Err("a Band not primitive".into()),
        _ => Ok(()),
    }
}

/// One random sequence of rows checked after each row: every point of the window is in the
/// hull iff every row holds there; the witness inside holds every row and the one outside
/// fails one; the hull is Empty only when no point of the window holds them, the plane only
/// when every row is trivial; and the invariants. With `bounded`, a box of 8 comes first, so
/// the window holds every point and Empty is checked exactly.
fn check_sequence(rng: &mut Rng, bounded: bool, w: i64) -> Result<(), String> {
    let mut rows: Vec<(Int, Int, Int)> = vec![];
    if bounded {
        rows.extend([row(1, 0, -8), row(-1, 0, -8), row(0, 1, -8), row(0, -1, -8)]);
    }
    let mut h = hull_of(&rows).ok_or("no hull of the box")?;
    for _ in 0..8 {
        let r = row(rng.small(4), rng.small(4), rng.small(6));
        rows.push(r.clone());
        h = add(&h, r.0, r.1, r.2).ok_or_else(|| format!("no hull: {rows:?}"))?;
        invariants(&h).map_err(|e| format!("{e}; rows {rows:?}; {h:?}"))?;
        let mut any = false;
        for x in -w..=w {
            for y in -w..=w {
                let p = (int(x), int(y));
                let want = holds_all(&rows, &p);
                any |= want;
                if contains(&h, &p) != want {
                    return Err(format!("{p:?}: want {want}; rows {rows:?}; {h:?}"));
                }
            }
        }
        match h.inside() {
            Some(p) if !holds_all(&rows, &p) => {
                return Err(format!("inside {p:?} fails; rows {rows:?}; {h:?}"));
            }
            None if !matches!(h, Hull::Empty) => return Err(format!("no inside: {h:?}")),
            Some(_) if matches!(h, Hull::Empty) => return Err("inside of Empty".into()),
            _ => {}
        }
        if matches!(h, Hull::Empty) && any {
            return Err(format!("Empty, but a point holds; rows {rows:?}"));
        }
        let trivial = (rows.iter()).all(|(a, b, c)| a.is_zero() && b.is_zero() && !c.is_positive());
        match h.outside() {
            Some(p) if holds_all(&rows, &p) => {
                return Err(format!("outside {p:?} holds; rows {rows:?}; {h:?}"));
            }
            None if !trivial => return Err(format!("no outside; rows {rows:?}; {h:?}")),
            Some(_) if trivial => return Err(format!("outside of the plane; {rows:?}")),
            _ => {}
        }
    }
    Ok(())
}

fn failures(seed: u64, runs: usize) -> Vec<String> {
    let mut rng = Rng(seed);
    let mut out = vec![];
    for i in 0..runs {
        let bounded = i % 2 == 0;
        if let Err(e) = check_sequence(&mut rng, bounded, if bounded { 9 } else { 24 }) {
            out.push(e);
        }
    }
    out
}

fn with_mutant<T>(m: u8, f: impl FnOnce() -> T) -> T {
    mutant::ON.with(|c| c.set(m));
    let out = f();
    mutant::ON.with(|c| c.set(mutant::NONE));
    out
}

#[test]
fn random_rows_give_the_integer_hull() {
    let f = failures(0x9e37_79b9_7f4a_7c15, 1500);
    assert!(f.is_empty(), "{} failures, the first: {}", f.len(), f[0]);
}

#[test]
fn each_step_mutant_is_caught() {
    // Design G5 / D12: each step disabled makes the random rows fail. Ties out of the run
    // (META3 H3) is caught by the tie test below as well.
    for m in [mutant::NO_CUTS, mutant::CASE1_IN_CASE2, mutant::NO_COLLAPSE] {
        let f = with_mutant(m, || failures(0x9e37_79b9_7f4a_7c15, 1500));
        let fixed = with_mutant(m, || hull_of(&case2_rows()));
        let caught = !f.is_empty() || fixed.as_ref().is_none_or(|h| invariants(h).is_err());
        assert!(caught, "mutant {m} not caught");
    }
}

/// Case 2 of step 5 (Gemini's instance, proto-r3/run.log line 44): the third row's section
/// holds no integer point, and case 1 there leaves a vertex that is not integral or a
/// redundant side (Case1InCase2 in the prototype: 103 not integral, 1023 redundant left).
/// Random rows reach case 2 rarely (877 of 80,130 rows in the prototype).
fn case2_rows() -> Vec<(Int, Int, Int)> {
    vec![row(5, 5, 7), row(0, -6, -2), row(-5, 3, -13)]
}

#[test]
fn case_two_gives_the_integer_hull() {
    let rows = case2_rows();
    counts::take();
    let h = hull_of(&rows).expect("a hull");
    assert!(counts::take()[counts::HULL_CASE2] > 0, "case 2 reached");
    invariants(&h).unwrap();
    for x in -12..=12 {
        for y in -12..=12 {
            let p = (int(x), int(y));
            assert_eq!(contains(&h, &p), holds_all(&rows, &p), "{p:?}: {h:?}");
        }
    }
}

#[test]
fn the_steps_are_counted() {
    counts::take();
    let f = failures(0x2545_f491_4f6c_dd1d, 400);
    let c = counts::take();
    assert!(f.is_empty(), "{f:?}");
    for (name, i) in [
        ("case 1", counts::HULL_CASE1),
        ("case 2", counts::HULL_CASE2),
        ("collapse", counts::HULL_COLLAPSE),
    ] {
        assert!(c[i] > 0, "no {name} in the random rows");
    }
}

/// The O(beta) walk of the cross-review's prototype (`proto-r3/hull.rs`, `pairwise`): the lower
/// hull of the least integer point on each lattice line `X = 0..=X*` of the corner, in the
/// coordinates of [`pairwise`].
fn pairwise_walk(e: &Row, c: &Row) -> Vec<Row> {
    let beta = cross(&e.n(), &c.n());
    let (_, s, t) = e.a.bezout(&e.b);
    let alpha = &(&c.a * &s) + &(&c.b * &t);
    let gamma = &c.c - &(&alpha * &e.c);
    let mut xs = int(0);
    while !(&gamma - &(&alpha * &xs)).mod_floor(&beta).is_zero() {
        xs = &xs + &int(1);
    }
    let mut hull: Vec<P> = vec![];
    let mut x = int(0);
    while x <= xs {
        let y = (&gamma - &(&alpha * &x)).div_ceil(&beta);
        let p = (x.clone(), y);
        while hull.len() >= 2 {
            let (o, a) = (&hull[hull.len() - 2], &hull[hull.len() - 1]);
            let turn = cross(&(&a.0 - &o.0, &a.1 - &o.1), &(&p.0 - &o.0, &p.1 - &o.1));
            if turn.is_positive() {
                break;
            }
            hull.pop();
        }
        hull.push(p);
        x = &x + &int(1);
    }
    corner_rows(e, &hull)
}

#[test]
fn the_corner_hull_is_the_walk() {
    let mut rng = Rng(0x1234_5678_9abc_def1);
    let mut cut = 0;
    for _ in 0..3000 {
        let (ea, eb, ca, cb) = (rng.small(9), rng.small(9), rng.small(9), rng.small(9));
        if (ea, eb) == (0, 0) || (ca, cb) == (0, 0) {
            continue;
        }
        let e = tighten(int(ea), int(eb), int(rng.small(30)));
        let c = tighten(int(ca), int(cb), int(rng.small(30)));
        if !cross(&e.n(), &c.n()).is_positive() {
            continue;
        }
        let got = pairwise(&e, &c);
        assert_eq!(got, pairwise_walk(&e, &c), "e {e:?}, c {c:?}");
        cut += (!got.is_empty()) as usize;
    }
    assert!(cut > 100, "only {cut} corners with cuts");
}

/// The hull of the tangents `y >= 2 i x - i²`, `i` in `0..k`, of `y = x²`, with `x <= k` and,
/// when `bounded`, `x >= 0` and `y <= k²`: vertices `(i, i²)`.
fn tangent_hull(k: i64, bounded: bool) -> Hull {
    let mut rows = vec![row(-1, 0, -k)];
    if bounded {
        rows.extend([row(1, 0, 0), row(0, -1, -k * k)]);
    }
    rows.extend((0..k).map(|i| row(-2 * i, 1, -i * i)));
    hull_of(&rows).expect("the tangent hull")
}

/// The run of `u` on `h`, by the searches and by the literal scan, with the tree nodes each
/// read; `None` when `u` keeps or empties `h`, where no run is read.
fn runs(h: &Hull, u: &Row) -> Option<((Vec<(usize, usize)>, u64), (Vec<(usize, usize)>, u64))> {
    let Hull::Poly { sides: t, bounded } = h else {
        return None;
    };
    let b = Boundary {
        sides: t,
        bounded: *bounded,
        u,
        k: size(t),
        bad: std::cell::Cell::new(false),
    };
    let (imax, imin) = (b.extreme(1), b.extreme(-1));
    if vs(&b.f(imin), &u.c) != Ordering::Less || vs(&b.f(imax), &u.c) != Ordering::Greater {
        return None;
    }
    counts::take();
    let fast = run(&b, imax, imin, &u.c);
    let nf = counts::take()[counts::HULL_NODES];
    let scan = run_by_scan(&b, &u.c);
    let ns = counts::take()[counts::HULL_NODES];
    Some(((fast, nf), (scan, ns)))
}

/// Rows through a vertex of the tangent hull (ties) and between, each against the scan.
fn tie_failures(k: i64, bounded: bool, max_nodes: u64) -> Vec<String> {
    let h = tangent_hull(k, bounded);
    let mut rng = Rng(0xdead_beef_cafe_f00d ^ k as u64);
    let mut out = vec![];
    for i in 0..200 {
        let (a, b) = (rng.small(5), rng.small(5));
        if a == 0 && b == 0 {
            continue;
        }
        let v = (rng.next() % k as u64) as i64;
        let tie = a * v + b * v * v;
        let c = if i % 2 == 0 { tie } else { tie + rng.small(3) };
        let u = tighten(int(a), int(b), int(c));
        let Some(((fast, nf), (scan, ns))) = runs(&h, &u) else {
            continue;
        };
        if fast != scan {
            out.push(format!("{u:?}: run {fast:?}, scan {scan:?}"));
        }
        if nf > max_nodes {
            out.push(format!("{u:?}: {nf} nodes read"));
        }
        if ns < k as u64 {
            out.push(format!("{u:?}: the scan read {ns} nodes"));
        }
    }
    out
}

#[test]
fn the_run_is_the_literal_scan_with_ties_in() {
    // META3 H3: the run against `<=` read position by position, rows through vertices half
    // the time, on a cycle and a path of about 2,000 sides; the run reads O(log k) nodes, the
    // scan at least k. Mutant: ties out of the run disagrees with the scan.
    for bounded in [true, false] {
        let f = tie_failures(2000, bounded, 400);
        assert!(
            f.is_empty(),
            "bounded {bounded}: {} failures: {:?}",
            f.len(),
            &f[..f.len().min(3)]
        );
        let f = with_mutant(mutant::TIES_OUT, || tie_failures(2000, bounded, 400));
        assert!(!f.is_empty(), "bounded {bounded}: ties out not caught");
    }
}

#[test]
fn a_translated_quadrant_keeps_its_rays() {
    // META3 H1, Codex B1: x >= 0, y >= 0, then x >= 5 keeps one vertex, (5, 0), and two
    // rays: a Polygon, not the Point (5, 0). Its witnesses are (5, 0) and a point outside;
    // then x <= 5 makes it the Line x = 5, y >= 0.
    let h = hull_of(&[row(1, 0, 0), row(0, 1, 0), row(1, 0, 5)]).expect("a hull");
    assert!(matches!(h, Hull::Poly { bounded: false, .. }), "{h:?}");
    assert_eq!(h.inside(), Some((int(5), int(0))));
    let out = h.outside().expect("a point outside");
    assert!(!contains(&h, &out), "{out:?}");
    assert!(contains(&h, &(int(5), int(7))));
    let l = add(&h, int(-1), int(0), int(-5)).expect("a hull");
    assert!(matches!(l, Hull::Line { .. }), "{l:?}");
    assert!(contains(&l, &(int(5), int(9))) && !contains(&l, &(int(4), int(9))));
    assert!(!contains(&l, &(int(5), int(-1))));
    // The triangle (0,0), (3,0), (0,3) cut by 2x + y >= 5 is the segment from (2, 1) to
    // (3, 0): a Line by the dimension check; with the check off, a Polygon of no area, caught
    // by the invariants (or no hull, where the solver would answer).
    let triangle = || hull_of(&[row(1, 0, 0), row(0, 1, 0), row(-1, -1, -3)]).expect("a triangle");
    let l = add(&triangle(), int(2), int(1), int(5)).expect("a hull");
    assert!(
        matches!(
            l,
            Hull::Line {
                lo: Some(_),
                hi: Some(_),
                ..
            }
        ),
        "{l:?}"
    );
    assert!(contains(&l, &(int(2), int(1))) && contains(&l, &(int(3), int(0))));
    assert!(!contains(&l, &(int(1), int(2))));
    let l = with_mutant(mutant::NO_COLLAPSE, || {
        add(&triangle(), int(2), int(1), int(5))
    });
    assert!(
        l.is_none_or(|l| invariants(&l).is_err()),
        "the mutant not caught"
    );
}

#[test]
fn rows_are_tightened_first() {
    // Step 1 (design D1): 1 <= 2x - 2y <= 1 has no integer point, though its region over Q is
    // the line x - y = 1/2.
    let h = hull_of(&[row(2, -2, 1), row(-2, 2, -1)]).expect("a hull");
    assert!(matches!(h, Hull::Empty), "{h:?}");
    // 3x + 3y >= 4 is x + y >= 2.
    let h = hull_of(&[row(3, 3, 4)]).expect("a hull");
    assert!(contains(&h, &(int(1), int(1))) && !contains(&h, &(int(1), int(0))));
}

#[test]
fn the_triangle_of_three_lattice_lines() {
    // META1 error 4: the triangle (0,0), (2,0), (0,2) cut by 2x + 2y >= 3 (x + y >= 2) is the
    // segment x + y = 2, 0 <= x <= 2; cut instead by x + 2y >= 1, it keeps four vertices.
    let t = [row(1, 0, 0), row(0, 1, 0), row(-1, -1, -2)];
    let mut rows = t.to_vec();
    rows.push(row(2, 2, 3));
    let h = hull_of(&rows).expect("a hull");
    assert!(
        matches!(
            h,
            Hull::Line {
                lo: Some(_),
                hi: Some(_),
                ..
            }
        ),
        "{h:?}"
    );
    for x in 0..=2 {
        assert!(contains(&h, &(int(x), int(2 - x))));
    }
    let mut rows = t.to_vec();
    rows.push(row(1, 2, 1));
    let h = hull_of(&rows).expect("a hull");
    let Hull::Poly {
        sides: s,
        bounded: true,
    } = &h
    else {
        panic!("{h:?}");
    };
    assert_eq!(size(s), 4, "{h:?}");
    // Then x >= 2: the Point (2, 0).
    rows.push(row(1, 0, 2));
    assert!(matches!(hull_of(&rows), Some(Hull::Point(p)) if p == (int(2), int(0))));
}

#[test]
fn a_hull_extended_twice_is_unchanged() {
    // Persistence (design D13): two rows added to one hull leave its sides as they were.
    let h = tangent_hull(300, true);
    let Hull::Poly { sides: t, .. } = &h else {
        panic!("{h:?}");
    };
    let before = sides(t);
    let a = add(&h, int(1), int(0), int(150)).expect("a hull");
    let b = add(&h, int(-1), int(0), int(-100)).expect("a hull");
    assert_eq!(sides(t), before);
    assert!(contains(&a, &(int(200), int(40_000))) && !contains(&a, &(int(100), int(10_000))));
    assert!(contains(&b, &(int(100), int(10_000))) && !contains(&b, &(int(200), int(40_000))));
}

/// The tree nodes read by `k` callers of the tangent hull of `k` sides, each adding one row
/// that cuts away between a quarter and three quarters of it (design D14), and the hull built.
fn callers_nodes(k: i64) -> u64 {
    counts::take();
    let h = tangent_hull(k, true);
    for c in 0..k {
        let r = if c % 2 == 0 {
            row(1, 0, k / 4 + c / 2)
        } else {
            row(-1, 0, -(3 * k / 4 - c / 2))
        };
        let g = add(&h, r.0, r.1, r.2).expect("a hull");
        assert!(g.inside().is_some());
    }
    counts::take()[counts::HULL_NODES]
}

#[test]
fn many_callers_read_few_nodes() {
    // Design D14 by tree nodes: k callers of one base of k sides at k = 2,000 and 8k; the run
    // and the splits read O(log k) nodes a caller, so the ratio is at most about
    // 8 log(8k) / log k = 10.19, under 10.5. The mutant reading every position (SCAN) reads
    // Θ(k) a caller, Θ(k²) in all, and is caught by the same limit; it is run at 100 and 800,
    // where its Θ(k²) nodes still fit the time of a test.
    let ratio = |m: u8, k: i64| {
        with_mutant(m, || {
            let (n1, n8) = (callers_nodes(k), callers_nodes(8 * k));
            n8 as f64 / n1 as f64
        })
    };
    let r = ratio(mutant::NONE, 2000);
    assert!(r <= 10.5, "nodes grew {r:.2} times from 2,000 to 16,000");
    let r = ratio(mutant::SCAN, 100);
    assert!(r > 10.5, "the scan grew only {r:.2} times");
}
