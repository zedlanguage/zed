//! Exact scalar images and translation-period orbits. Scalar certificates read one
//! value; the orbit certificate additionally retains its original input remainder.
//! Other joint questions continue to use the relational summaries with all their inputs.

use super::*;
use zedc_int::int::Num;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Image {
    /// Prefix maxima on this input axis are cofinal and rise by at most one.
    Prefix(Atom),
    /// All integers, without the stronger prefix-maximum invariant.
    All,
    /// Exactly 2^e Z. The exponent is saturated by the modulus, never expanded.
    Power(usize),
    /// Image of k repetitions of h + (if h mod m == 0 then 1 else 2).
    Skipping(Arc<Int>, Int),
    Clamp(Arc<ClampBasis>, usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ClampBasis {
    axis: Atom,
    a: Int,
    b: Int,
    constant: Int,
}
impl ClampBasis {
    fn value(&self, x: &Int) -> Int {
        &(&x.div_floor(&self.a) + &x.div_floor(&self.b)) + &self.constant
    }
    // Complexity tradeoff: expanding k floor contractions builds k-bit coefficients and
    // graph projections. Invert the original two-floor clamp by a monotone cut instead:
    // its error from x*(a+b)/(a*b) is less than two, giving an O(min(a,b))-wide bracket.
    // Binary search uses O(log(min(a,b)+1)) arithmetic operations, independent of k;
    // numeric operand cost is charged at the original divisor/target bit width.
    fn cut(&self, c: &Int) -> Int {
        let numerator = &self.a * &self.b;
        let denominator = &self.a + &self.b;
        let target = c - &self.constant;
        let mut lo = (&(&target - &Int::from(2)) * &numerator).div_floor(&denominator);
        let mut hi = -(&(-&(&(&target + &Int::from(2)) * &numerator)).div_floor(&denominator));
        while &hi - &lo > Int::ONE {
            let mid = (&lo + &hi).div_floor(&Int::from(2));
            if self.value(&mid) >= *c {
                hi = mid;
            } else {
                lo = mid;
            }
        }
        hi
    }
    // Complexity tradeoff: constructing 2^k*c takes k coefficient bits even when the
    // min is already the fixed original cut. Saturate exact doubling at that cut:
    // O(min(k, log(1+abs(cut)))) arithmetic operations for positive c, O(1) for zero
    // and the k=1 negative case. No iterate or literal grows beyond the cut's width.
    fn chain_cut(&self, c: &Int, k: usize) -> Int {
        let cut = self.cut(c);
        if c.is_negative() {
            return (c * &Int::from(2)).min(cut);
        }
        if c.is_zero() {
            return Int::ZERO.min(cut);
        }
        // Saturate the product as soon as the minimum is known. The iteration is
        // bounded by the original numeric bit width, not by an arbitrary pass budget.
        let mut x = c.clone();
        let mut left = k;
        while left > 0 && x < cut {
            x = &x * &Int::from(2);
            left -= 1;
        }
        x.min(cut)
    }
    fn contains(&self, c: &Int, k: usize) -> bool {
        // Below zero, B/2^(k-1) has jumps at most one for k>=2. Together with
        // floor(x/2^k) it reaches every negative integer before B becomes positive.
        if k >= 2 && c.is_negative() {
            return true;
        }
        self.chain_cut(c, k) < self.chain_cut(&(c + &Int::ONE), k)
    }
}

impl Image {
    fn exponent(&self) -> Option<usize> {
        match self {
            Self::Prefix(_) | Self::All => Some(0),
            Self::Power(e) => Some(*e),
            _ => None,
        }
    }

    fn contains(&self, c: &Int) -> bool {
        match self {
            Self::Prefix(_) | Self::All => true,
            Self::Power(e) => c.is_zero() || twos(c).is_some_and(|z| z >= *e),
            Self::Clamp(b, k) => b.contains(c, *k),
            Self::Skipping(m, k) => {
                let r = c.mod_floor(m);
                r.is_odd()
                    || (r.is_zero() && m.is_odd())
                    || (!r.is_zero() && &(&Int::from(2) * k) < &r)
                    || (r.is_zero() && !m.is_odd() && &(&Int::from(2) * k) < &**m)
            }
        }
    }
}

fn twos(x: &Int) -> Option<usize> {
    if x.is_zero() {
        return None;
    }
    usize::try_from(Num::from(x).trailing_zeros().to_i128()?).ok()
}

#[derive(Clone, Default)]
struct Fact {
    image: Option<Image>,
    /// The exact quotient (true) or remainder (false) of this dividend and divisor.
    division: Option<(bool, Lin, Arc<Int>)>,
}

#[derive(Default)]
pub(super) struct ScalarImages {
    done: HashSet<Id>,
    by: HashMap<Atom, Fact>,
    orbits: HashMap<Atom, Orbit>,
    orbit_done: HashSet<Id>,
}

#[derive(Clone)]
struct Orbit {
    axis: Atom,
    modulus: Arc<Int>,
    steps: Int,
    skipping: bool,
    multiplier: Int,
}

impl Orbit {
    /// The output residue after all steps from this exact input residue.
    fn residue(&self, r: &Int) -> Int {
        let m = &self.modulus;
        if !self.skipping {
            return (&self.multiplier * r).mod_floor(m);
        }
        let visits = if !m.is_odd() {
            let first = (-r).mod_floor(m).div_floor(&Int::from(2));
            if r.is_odd() || self.steps <= first {
                Int::ZERO
            } else {
                Int::ONE
            }
        } else {
            let period = (&**m + &Int::ONE).div_floor(&Int::from(2));
            let first = (&(-r) * &period).mod_floor(m);
            if self.steps <= first {
                Int::ZERO
            } else {
                &Int::ONE + &(&(&self.steps - &Int::ONE) - &first).div_floor(&period)
            }
        };
        (&(r + &(&Int::from(2) * &self.steps)) - &visits).mod_floor(m)
    }
}

// Complexity tradeoff: advancing d relative steps explicitly is O(d). Binary modular
// powering is O(log(d+1)) arithmetic operations on O(log M)-bit residues. Adjacent
// links need one step; original-input queries reuse the cached orbit multiplier.
fn power_two_mod(exponent: &Int, modulus: &Int) -> Int {
    let mut exponent = exponent.clone();
    let mut base = Int::from(2).mod_floor(modulus);
    let mut out = Int::ONE.mod_floor(modulus);
    while !exponent.is_zero() {
        if exponent.is_odd() {
            out = (&out * &base).mod_floor(modulus);
        }
        exponent = exponent.div_floor(&Int::from(2));
        if !exponent.is_zero() {
            base = (&base * &base).mod_floor(modulus);
        }
    }
    out
}

/// A unit equation for the sole output, with no other constraint.
fn value_equation(f: &Formula, output: &Atom) -> Option<Lin> {
    let f = match f {
        Formula::And(gs) => match gs.as_slice() {
            [g] => g,
            _ => return None,
        },
        _ => f,
    };
    let Formula::Con(c) = f else { return None };
    if c.rel != Rel::Eq {
        return None;
    }
    let k = c.lin.terms.get(output)?;
    if !k.is_unit() {
        return None;
    }
    let mut value = c.lin.clone();
    value.terms.remove(output);
    Some(value.times(-k))
}

/// An if whose guards are literal complements and whose arms each give one value.
/// The positive guard is returned first, independent of the written arm order.
fn choice(f: &Formula, output: &Atom) -> Option<(Formula, Lin, Lin)> {
    let Formula::Or(gs) = f else { return None };
    let [left, right] = gs.as_slice() else {
        return None;
    };
    let branch = |g: &Formula| -> Option<(Formula, Lin)> {
        let Formula::And(parts) = g else { return None };
        let [a, b] = parts.as_slice() else {
            return None;
        };
        let (guard, value) = if let Some(e) = value_equation(a, output) {
            (b, e)
        } else {
            (a, value_equation(b, output)?)
        };
        if reads(guard).contains(output) {
            return None;
        }
        Some((guard.clone(), value))
    };
    let (g, a) = branch(left)?;
    let (h, b) = branch(right)?;
    if let Formula::Not(n) = &h
        && **n == g
    {
        return Some((g, a, b));
    }
    if let Formula::Not(n) = &g
        && **n == h
    {
        return Some((h, b, a));
    }
    None
}

/// Exact Euclidean division, including negative divisors. The remainder is nonnegative.
fn division(d: &Def) -> Option<(Atom, Atom, Lin, Int)> {
    let [u, v] = d.own.as_slice() else {
        return None;
    };
    let Formula::And(gs) = &d.f else { return None };
    let [_, _, _] = gs.as_slice() else {
        return None;
    };
    let rows: Option<Vec<&Con>> = gs
        .iter()
        .map(|g| match g {
            Formula::Con(c) => Some(c),
            _ => None,
        })
        .collect();
    let rows = rows?;
    for (q, r) in [(*u, *v), (*v, *u)] {
        let (q, r) = (Atom::Aux(q), Atom::Aux(r));
        let eq = rows.iter().find(|c| c.rel == Rel::Eq)?;
        let kr = eq.lin.terms.get(&r)?;
        if !kr.is_unit() {
            continue;
        }
        let m = eq.lin.terms.get(&q)? * kr;
        if m.is_zero() {
            continue;
        }
        let mut arg = eq.lin.clone();
        arg.terms.remove(&q);
        arg.terms.remove(&r);
        arg = arg.times(-kr);
        let bound = &m.abs() - &Int::ONE;
        let lo = Con::ge(&Lin::atom(r.clone()), &Lin::constant(0));
        let hi = Con::ge(&Lin::constant(bound), &Lin::atom(r.clone()));
        if rows.iter().any(|c| **c == lo) && rows.iter().any(|c| **c == hi) {
            return Some((q, r, arg, m));
        }
    }
    None
}

impl ScalarImages {
    // Complexity tradeoff: graph summaries of periodic chains enumerate residues and
    // growing coefficients, quadratic or worse for I34/I42 equality. These exact scalar
    // descriptors store an input axis, a saturated lattice exponent, or (modulus, depth).
    // Postorder caching visits V+E definitions once, with local O(T log T) pattern work,
    // O(log depth)-bit counters and arithmetic on original coefficients. The two-floor
    // clamp additionally pays its original-divisor logarithmic cut search, below.
    // No cases or
    // numerical residue interval is enumerated. Unsupported or joint questions use the
    // existing exact graph path; this does not replace a joint relation by a scalar image.
    pub(super) fn answer(&mut self, f: &Formula, def: &dyn Fn(u32) -> Formula) -> Option<bool> {
        if matches!(f, Formula::And(_))
            || matches!(f,Formula::Not(g) if matches!(&**g,Formula::And(_)))
        {
            return self.joint(f, def);
        }
        let (row, negated) = match f {
            Formula::Con(c) if c.rel == Rel::Eq => (c, false),
            Formula::Not(g) => match &**g {
                Formula::Con(c) if c.rel == Rel::Eq => (c, true),
                _ => return None,
            },
            _ => return None,
        };
        if row.lin.terms.len() != 1 {
            return None;
        }
        let (a, k) = row.lin.terms.first_key_value()?;
        if k.is_zero() || matches!(a, Atom::Product(..)) {
            return None;
        }
        if let Atom::Aux(n) = a {
            self.ensure(def(*n), def);
        }
        let image = self.fact(a, def)?.image?;
        // Every supported image is infinite, so it always has a value unequal to c.
        if negated {
            return Some(true);
        }
        let dividend = -&row.lin.constant;
        if !dividend.mod_floor(k).is_zero() {
            return Some(false);
        }
        Some(image.contains(&dividend.div_floor(k)))
    }

    fn fact(&self, a: &Atom, def: &dyn Fn(u32) -> Formula) -> Option<Fact> {
        match a {
            Atom::Sym(_) => Some(Fact {
                image: Some(Image::Prefix(a.clone())),
                division: None,
            }),
            Atom::Aux(n) if free(&def(*n)) => Some(Fact {
                image: Some(Image::Prefix(a.clone())),
                division: None,
            }),
            _ => self.by.get(a).cloned(),
        }
    }

    fn linear(&self, e: &Lin, def: &dyn Fn(u32) -> Formula) -> Option<Fact> {
        if let [(a, k)] = e.terms.iter().collect::<Vec<_>>().as_slice() {
            let fact = self.fact(a, def)?;
            if **k == Int::ONE && e.constant.is_zero() {
                return Some(fact);
            }
            if k.is_unit() {
                let image = match fact.image? {
                    Image::Prefix(axis) if k.is_positive() => Image::Prefix(axis),
                    Image::Prefix(_) | Image::All | Image::Power(0) => Image::All,
                    _ => return None,
                };
                return Some(Fact {
                    image: Some(image),
                    division: None,
                });
            }
        }
        let terms: Vec<_> = e.terms.iter().collect();
        let [(a, ka), (b, kb)] = terms.as_slice() else {
            return None;
        };
        for (r, kr, other, ko) in [(*a, *ka, *b, *kb), (*b, *kb, *a, *ka)] {
            let Some((false, arg, m)) = self.fact(r, def).and_then(|v| v.division) else {
                continue;
            };
            // h + h mod m, with the same h, not merely two equal scalar ranges.
            if *kr == Int::ONE
                && *ko == Int::ONE
                && e.constant.is_zero()
                && arg == Lin::atom(other.clone())
                && m.is_positive()
            {
                let exponent = self.fact(other, def)?.image?.exponent()?;
                let z = twos(&m)?;
                if exponent <= z {
                    let next = if exponent < z { exponent + 1 } else { exponent };
                    return Some(Fact {
                        image: Some(Image::Power(next)),
                        division: None,
                    });
                }
            }
            // w*(x mod M) + floor(x/D) + C has consecutive prefix records for M<=D.
            let Some((true, qarg, divisor)) = self.fact(other, def).and_then(|v| v.division) else {
                continue;
            };
            if *ko != Int::ONE || arg != qarg || !m.is_positive() || *m > *divisor {
                continue;
            }
            let Some(axis) = lone_atom(&arg) else {
                continue;
            };
            if !matches!(axis, Atom::Sym(_)) && !matches!(axis, Atom::Aux(n) if free(&def(*n))) {
                continue;
            }
            return Some(Fact {
                image: Some(Image::Prefix(axis.clone())),
                division: None,
            });
        }
        None
    }

    fn ensure(&mut self, root: Formula, def: &dyn Fn(u32) -> Formula) {
        if free(&root) {
            return;
        }
        let mut stack = vec![(root, false)];
        let mut open = HashSet::new();
        while let Some((f, exit)) = stack.pop() {
            let id = Id::any(&f);
            if self.done.contains(&id) || free(&f) {
                continue;
            }
            let Some(d) = Def::of(f.clone(), def) else {
                self.done.insert(id);
                continue;
            };
            if !exit {
                if !open.insert(id) {
                    self.done.insert(id);
                    continue;
                }
                stack.push((f, true));
                let mut seen = HashSet::new();
                for &n in d.inputs.iter().rev() {
                    let child = def(n);
                    if seen.insert(Id::any(&child)) {
                        stack.push((child, false));
                    }
                }
                continue;
            }
            open.remove(&id);
            if let Some((q, r, arg, m)) = division(&d) {
                let image = if m.is_positive() {
                    self.linear(&arg, def)
                        .and_then(|f| f.image)
                        .and_then(|i| match i {
                            Image::Prefix(axis) => Some(Image::Prefix(axis)),
                            _ => None,
                        })
                } else {
                    None
                };
                let m = Arc::new(m);
                self.by.insert(
                    q,
                    Fact {
                        image,
                        division: Some((true, arg.clone(), Arc::clone(&m))),
                    },
                );
                self.by.insert(
                    r,
                    Fact {
                        image: None,
                        division: Some((false, arg, m)),
                    },
                );
            } else if let [n] = d.own.as_slice() {
                let output = Atom::Aux(*n);
                let fact = if let Some(e) = value_equation(&d.f, &output) {
                    self.linear(&e, def)
                } else if let Some((guard, left, right)) = choice(&d.f, &output) {
                    self.choice_image(&guard, &left, &right, def)
                } else {
                    None
                };
                self.by.insert(output, fact.unwrap_or_default());
            }
            self.done.insert(id);
        }
    }

    // Orbit metadata is demanded only by a correlated period question; ordinary scalar
    // equality pays for scalar facts alone. Both postorders have visited caches.
    fn ensure_orbits(&mut self, root: Formula, def: &dyn Fn(u32) -> Formula) {
        let mut stack = vec![(root, false)];
        let mut open = HashSet::new();
        while let Some((f, exit)) = stack.pop() {
            if free(&f) {
                continue;
            }
            let id = Id::any(&f);
            if self.orbit_done.contains(&id) {
                continue;
            }
            let Some(d) = Def::of(f.clone(), def) else {
                self.orbit_done.insert(id);
                continue;
            };
            if !exit {
                if !open.insert(id) {
                    self.orbit_done.insert(id);
                    continue;
                }
                stack.push((f, true));
                let mut seen = HashSet::new();
                for &n in d.inputs.iter().rev() {
                    let child = def(n);
                    if seen.insert(Id::any(&child)) {
                        stack.push((child, false));
                    }
                }
            } else {
                open.remove(&id);
                if let [n] = d.own.as_slice() {
                    self.record_orbit(Atom::Aux(*n), &d.f, def);
                }
                self.orbit_done.insert(id);
            }
        }
    }

    fn record_orbit(&mut self, output: Atom, f: &Formula, def: &dyn Fn(u32) -> Formula) {
        let step = (|| {
            if let Some(value) = value_equation(f, &output) {
                if let Some(input) = lone_atom(&value) {
                    if let Some(old) = self.orbits.get(input).cloned() {
                        self.orbits.insert(output.clone(), old);
                    }
                    return None;
                }
                if !value.constant.is_zero()
                    || value.terms.len() != 2
                    || value.terms.values().any(|k| *k != Int::ONE)
                {
                    return None;
                }
                for r in value.terms.keys() {
                    let Some((false, arg, m)) = self.fact(r, def).and_then(|f| f.division) else {
                        continue;
                    };
                    let Some(input) = lone_atom(&arg) else {
                        continue;
                    };
                    if value == arg.plus(&Lin::atom(r.clone())) {
                        return Some((input.clone(), m, false));
                    }
                }
                None
            } else {
                let (guard, left, right) = choice(f, &output)?;
                let Formula::Con(ref c) = guard else {
                    return None;
                };
                if c.rel != Rel::Eq {
                    return None;
                }
                let r = zero_atom(&c.lin)?;
                let (false, arg, m) = self.fact(r, def)?.division? else {
                    return None;
                };
                if left != arg.plus(&Lin::constant(1)) || right != arg.plus(&Lin::constant(2)) {
                    return None;
                }
                Some((lone_atom(&arg)?.clone(), m, true))
            }
        })();
        let Some((input, m, skipping)) = step else {
            return;
        };
        if !m.is_positive() {
            return;
        }
        let old =
            if matches!(&input, Atom::Sym(_)) || matches!(&input,Atom::Aux(n) if free(&def(*n))) {
                Some(Orbit {
                    axis: input.clone(),
                    modulus: Arc::clone(&m),
                    steps: Int::ZERO,
                    skipping,
                    multiplier: Int::ONE,
                })
            } else {
                self.orbits.get(&input).cloned()
            };
        let Some(mut old) = old else { return };
        if old.modulus != m || old.skipping != skipping {
            return;
        }
        old.steps = &old.steps + &Int::ONE;
        if !skipping {
            old.multiplier = (&old.multiplier * &Int::from(2)).mod_floor(&m);
        }
        self.orbits.insert(output, old);
    }

    // Complexity tradeoff: graph splitting on each individual input residue can cost
    // n*min(n,M) or worse (I34/I42). Retain a certified translation-period orbit as
    // (input axis, modulus, count), and for doubling also 2^count modulo M. A question
    // fixing an input/ancestor remainder and output tests this exact period relation using
    // O(1) arithmetic operations for adjacent/original-input links, O(log d) for a
    // distance-d doubling query, on O(log count+log M)-bit values.
    // No residue enumeration or growing 2^count literal. Other joint keys use graphs.
    fn joint(&mut self, f: &Formula, def: &dyn Fn(u32) -> Formula) -> Option<bool> {
        let (g, negated) = match f {
            Formula::Not(g) => (&**g, true),
            g => (g, false),
        };
        let Formula::And(parts) = g else { return None };
        let [left, right] = parts.as_slice() else {
            return None;
        };
        let equation = |f: &Formula| -> Option<(Atom, Int)> {
            let Formula::Con(c) = f else { return None };
            if c.rel != Rel::Eq || c.lin.terms.len() != 1 {
                return None;
            }
            let (a, k) = c.lin.terms.first_key_value()?;
            let v = -&c.lin.constant;
            if k.is_zero() || !v.mod_floor(k).is_zero() {
                return None;
            }
            Some((a.clone(), v.div_floor(k)))
        };
        let (a, c) = equation(left)?;
        let (b, s) = equation(right)?;
        if !matches!(a, Atom::Aux(_)) || !matches!(b, Atom::Aux(_)) {
            return None;
        }
        for atom in [&a, &b] {
            if let Atom::Aux(n) = atom {
                self.ensure(def(*n), def);
            }
        }
        for (output, c, remainder, s) in [(&a, &c, &b, &s), (&b, &s, &a, &c)] {
            let Some((false, arg, m)) = self.fact(remainder, def).and_then(|f| f.division) else {
                continue;
            };
            if let Atom::Aux(n) = output {
                self.ensure_orbits(def(*n), def);
            }
            let Some(orbit) = self.orbits.get(output).cloned() else {
                continue;
            };
            if m != orbit.modulus {
                continue;
            }
            let Some(input) = lone_atom(&arg) else {
                continue;
            };
            let ancestor = if *input == orbit.axis {
                Orbit {
                    axis: orbit.axis.clone(),
                    modulus: Arc::clone(&m),
                    steps: Int::ZERO,
                    skipping: orbit.skipping,
                    multiplier: Int::ONE,
                }
            } else {
                if let Atom::Aux(n) = input {
                    self.ensure_orbits(def(*n), def);
                }
                let Some(old) = self.orbits.get(input).cloned() else {
                    continue;
                };
                if old.axis != orbit.axis || old.modulus != m || old.skipping != orbit.skipping {
                    continue;
                }
                old
            };
            let (Some(input_image), Some(output_image)) = (
                self.fact(input, def).and_then(|v| v.image),
                self.fact(output, def).and_then(|v| v.image),
            ) else {
                continue;
            };
            // Both scalar images are M-periodic and each orbit commutes with +M.
            // If the fixed residue belongs to the earlier image, every integer lift
            // of it is realizable; exactly one lift gives the requested later value.
            // In the other direction, a realizable fixed value determines its future.
            if negated {
                return Some(true);
            }
            if s.is_negative() || s >= &*m {
                return Some(false);
            }
            if orbit.steps >= ancestor.steps {
                let count = &orbit.steps - &ancestor.steps;
                let mut relative = orbit.clone();
                relative.steps = count.clone();
                if !relative.skipping && count != orbit.steps {
                    relative.multiplier = power_two_mod(&count, &m);
                }
                return Some(input_image.contains(s) && relative.residue(s) == c.mod_floor(&m));
            } else {
                let mut relative = ancestor.clone();
                relative.steps = &ancestor.steps - &orbit.steps;
                if !relative.skipping {
                    relative.multiplier = power_two_mod(&relative.steps, &m);
                }
                return Some(output_image.contains(c) && relative.residue(&c.mod_floor(&m)) == *s);
            }
        }
        None
    }

    // Complexity tradeoff: graph summaries of this clamp retain growing dyadic
    // coefficients. Store the two original positive divisors, offset and link count.
    // Each equality uses two monotone cuts, O(log min(a,b)) arithmetic steps plus
    // saturation bounded by the original target/divisor bits; no 2^depth is built.
    fn clamp_image(&self, left: &Lin, right: &Lin, def: &dyn Fn(u32) -> Formula) -> Option<Fact> {
        for (half, bound) in [(left, right), (right, left)] {
            let Some((true, arg, m)) = self.linear(half, def).and_then(|f| f.division) else {
                continue;
            };
            if *m != Int::from(2) {
                continue;
            }
            let old = lone_atom(&arg)?;
            if bound.terms.len() != 2 || bound.terms.values().any(|k| *k != Int::ONE) {
                continue;
            }
            let mut quotients = Vec::new();
            for q in bound.terms.keys() {
                let (true, arg, m) = self.fact(q, def)?.division? else {
                    return None;
                };
                if !m.is_positive() {
                    return None;
                }
                quotients.push((arg, m));
            }
            if quotients[0].0 != quotients[1].0 {
                return None;
            }
            let axis = lone_atom(&quotients[0].0)?.clone();
            if !matches!(&axis, Atom::Sym(_)) && !matches!(&axis,Atom::Aux(n) if free(&def(*n))) {
                return None;
            }
            let mut ds = [(*quotients[0].1).clone(), (*quotients[1].1).clone()];
            ds.sort();
            let basis = ClampBasis {
                axis: axis.clone(),
                a: ds[0].clone(),
                b: ds[1].clone(),
                constant: bound.constant.clone(),
            };
            let k = match self.fact(old, def)?.image? {
                Image::Clamp(b, k) if *b == basis => k + 1,
                _ if *old == axis => 1,
                _ if matches!(old,Atom::Aux(n) if value_equation(&def(*n),old)==Some(Lin::atom(axis.clone()))) => {
                    1
                }
                _ => return None,
            };
            return Some(Fact {
                image: Some(Image::Clamp(Arc::new(basis), k)),
                division: None,
            });
        }
        None
    }

    fn choice_image(
        &self,
        guard: &Formula,
        left: &Lin,
        right: &Lin,
        def: &dyn Fn(u32) -> Formula,
    ) -> Option<Fact> {
        let Formula::Con(c) = guard else { return None };
        if c.rel == Rel::Ge && c.lin == left.minus(right) {
            if let (Some(Image::Prefix(a)), Some(Image::Prefix(b))) = (
                self.linear(left, def).and_then(|f| f.image),
                self.linear(right, def).and_then(|f| f.image),
            ) && a == b
            {
                return Some(Fact {
                    image: Some(Image::Prefix(a)),
                    division: None,
                });
            }
            if let Some(fact) = self.clamp_image(left, right, def) {
                return Some(fact);
            }
        }
        if c.rel != Rel::Eq || !c.lin.constant.is_zero() {
            return None;
        }
        let r = zero_atom(&c.lin)?;
        let (false, arg, m) = self.fact(r, def)?.division? else {
            return None;
        };
        if !m.is_positive()
            || *left != arg.plus(&Lin::constant(1))
            || *right != arg.plus(&Lin::constant(2))
        {
            return None;
        }
        let image = self.linear(&arg, def)?.image?;
        let k = match image {
            Image::Prefix(_) | Image::All | Image::Power(0) => Int::ONE,
            Image::Skipping(old, k) if old == m => &k + &Int::ONE,
            _ => return None,
        };
        Some(Fact {
            image: Some(Image::Skipping(m, k)),
            division: None,
        })
    }
}

fn lone_atom(e: &Lin) -> Option<&Atom> {
    if !e.constant.is_zero() || e.terms.len() != 1 {
        return None;
    }
    let (a, k) = e.terms.first_key_value()?;
    (*k == Int::ONE).then_some(a)
}

fn zero_atom(e: &Lin) -> Option<&Atom> {
    if !e.constant.is_zero() || e.terms.len() != 1 {
        return None;
    }
    let (a, k) = e.terms.first_key_value()?;
    (!k.is_zero()).then_some(a)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn descriptors_agree_with_explicit_residue_images() {
        let mut checked = 0;
        let mut wrong_all = 0;
        for m in 1i64..=41 {
            let modulus = Arc::new(Int::from(m));
            let mut skipping: BTreeSet<i64> = (0..m).collect();
            let mut doubling = skipping.clone();
            let mut exponent = 0;
            for k in 0..=2 * m {
                let skip = Image::Skipping(Arc::clone(&modulus), Int::from(k));
                let power = Image::Power(exponent);
                for c in -2 * m..=2 * m {
                    let r = c.rem_euclid(m);
                    assert_eq!(
                        skip.contains(&Int::from(c)),
                        skipping.contains(&r),
                        "skip M={m}, k={k}, c={c}"
                    );
                    assert_eq!(
                        power.contains(&Int::from(c)),
                        doubling.contains(&r),
                        "double M={m}, k={k}, c={c}"
                    );
                    wrong_all +=
                        usize::from(!skipping.contains(&r)) + usize::from(!doubling.contains(&r));
                    checked += 2;
                }
                skipping = skipping
                    .into_iter()
                    .map(|r| (r + if r == 0 { 1 } else { 2 }) % m)
                    .collect();
                doubling = doubling.into_iter().map(|r| 2 * r % m).collect();
                let z = m.trailing_zeros() as usize;
                if exponent < z {
                    exponent += 1;
                }
            }
        }
        assert!(wrong_all > 0);
        eprintln!("scalar descriptor checks={checked}, false all-integers control={wrong_all}");
    }

    fn chain(m: i64, count: usize, skip: bool) -> (Vec<Formula>, Vec<Atom>) {
        let mut defs = Vec::new();
        let mut outputs = Vec::new();
        let mut input = Lin::atom(Atom::Sym("x".into()));
        for _ in 0..count {
            let n = defs.len() as u32;
            let q = Lin::atom(Atom::Aux(n));
            let r = Lin::atom(Atom::Aux(n + 1));
            let pair = Formula::And(Shared::new(vec![
                Formula::Con(Con::eq(&input, &q.times(m).plus(&r))),
                Formula::Con(Con::ge(&r, &Lin::constant(0))),
                Formula::Con(Con::ge(&Lin::constant(m - 1), &r)),
            ]));
            defs.push(pair.clone());
            defs.push(pair);
            let output = Atom::Aux(n + 2);
            let out = Lin::atom(output.clone());
            let f = if skip {
                let guard = Formula::Con(Con::eq(&r, &Lin::constant(0)));
                Formula::Or(Shared::new(vec![
                    Formula::and(vec![
                        guard.clone(),
                        Formula::Con(Con::eq(&out, &input.plus(&Lin::constant(1)))),
                    ]),
                    Formula::and(vec![
                        Formula::negate(guard),
                        Formula::Con(Con::eq(&out, &input.plus(&Lin::constant(2)))),
                    ]),
                ]))
            } else {
                Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                    &out,
                    &input.plus(&r),
                ))]))
            };
            defs.push(f);
            outputs.push(output);
            input = out;
        }
        (defs, outputs)
    }

    #[test]
    fn images_are_scalar_only_and_do_not_forget_correlations() {
        for skip in [false, true] {
            for m in [2, 7, 8, 1000, 1_000_000_007] {
                let (defs, outputs) = chain(m, 7, skip);
                let def = |n: u32| defs[n as usize].clone();
                let mut images = ScalarImages::default();
                for (i, a) in outputs.iter().enumerate() {
                    for c in -17i64..=17 {
                        let q = Formula::Con(Con::eq(&Lin::atom(a.clone()), &Lin::constant(c)));
                        let mut predecessors = BTreeSet::from([c]);
                        for _ in 0..=i {
                            let mut next = BTreeSet::new();
                            for y in predecessors {
                                if skip {
                                    if (y - 1).rem_euclid(m) == 0 {
                                        next.insert(y - 1);
                                    }
                                    if (y - 2).rem_euclid(m) != 0 {
                                        next.insert(y - 2);
                                    }
                                } else {
                                    let top = y.div_euclid(m);
                                    for q in [top - 1, top] {
                                        let twice_r = y - m * q;
                                        if twice_r >= 0
                                            && twice_r <= 2 * (m - 1)
                                            && twice_r % 2 == 0
                                        {
                                            next.insert(m * q + twice_r / 2);
                                        }
                                    }
                                }
                            }
                            predecessors = next;
                        }
                        let expected = !predecessors.is_empty();
                        assert_eq!(
                            images.answer(&q, &def),
                            Some(expected),
                            "M={m}, k={}, skip={skip}, c={c}",
                            i + 1
                        );
                        let joint = Formula::and(vec![
                            q,
                            Formula::Con(Con::eq(
                                &Lin::atom(Atom::Sym("x".into())),
                                &Lin::constant(0),
                            )),
                        ]);
                        assert_eq!(images.answer(&joint, &def), None);
                    }
                }
            }
        }
        // The guard D|M is necessary: the image of 2Z under h+h mod 3 is not a lattice.
        let r = Atom::Aux(1);
        let h = Atom::Aux(0);
        let mut images = ScalarImages::default();
        images.by.insert(
            h.clone(),
            Fact {
                image: Some(Image::Power(1)),
                division: None,
            },
        );
        images.by.insert(
            r.clone(),
            Fact {
                image: None,
                division: Some((false, Lin::atom(h.clone()), Arc::new(Int::from(3)))),
            },
        );
        assert!(
            images
                .linear(&Lin::atom(h).plus(&Lin::atom(r)), &|_| Formula::bottom())
                .is_none()
        );
    }

    #[test]
    fn partial_and_product_definitions_do_not_get_scalar_images() {
        let x = Lin::atom(Atom::Sym("x".into()));
        let v = Atom::Aux(0);
        let partial = Formula::And(Shared::new(vec![
            Formula::Con(Con::eq(&Lin::atom(v), &x)),
            Formula::Con(Con::ge(&x, &Lin::constant(0))),
        ]));
        let question = Formula::Con(Con::eq(&Lin::atom(Atom::Aux(0)), &Lin::constant(9)));
        assert_eq!(
            ScalarImages::default().answer(&question, &|_| partial.clone()),
            None
        );
        let (defs, _) = chain(7, 1, true);
        let def = |n: u32| defs[n as usize].clone();
        assert!(
            ScalarImages::default()
                .answer(
                    &Formula::Con(Con::eq(&Lin::atom(Atom::Aux(2)), &Lin::constant(1))),
                    &def
                )
                .is_some()
        );
        let product = Lin::atom(Atom::Product(
            Factor::Sym("x".into()),
            Factor::Sym("y".into()),
        ));
        let f = Formula::And(Shared::new(vec![Formula::Con(Con::eq(
            &Lin::atom(Atom::Aux(0)),
            &product,
        ))]));
        assert_eq!(
            ScalarImages::default().answer(&question, &|_| f.clone()),
            None
        );
    }

    #[test]
    fn orbit_questions_keep_the_original_input_residue() {
        let mut checked = 0;
        for m in [7i64, 1000, 1_000_000_007] {
            for skip in [false, true] {
                let (defs, outputs) = chain(m, 640, skip);
                let def = |n: u32| defs[n as usize].clone();
                let mut images = ScalarImages::default();
                let mut values = BTreeMap::from([(0i64, 0i64), (3, 3), (m - 1, m - 1)]);
                for output in outputs {
                    for (&r, y) in &mut values {
                        *y = if skip {
                            *y + if y.rem_euclid(m) == 0 { 1 } else { 2 }
                        } else {
                            *y + y.rem_euclid(m)
                        };
                        // Keep the independently evaluated orbit modulo M, avoiding
                        // overflow in this native test as well as in the certificate.
                        *y = y.rem_euclid(m);
                        for c in [0i64, 9] {
                            let q = Formula::and(vec![
                                Formula::Con(Con::eq(
                                    &Lin::atom(output.clone()),
                                    &Lin::constant(c),
                                )),
                                Formula::Con(Con::eq(&Lin::atom(Atom::Aux(1)), &Lin::constant(r))),
                            ]);
                            assert_eq!(
                                images.answer(&q, &def),
                                Some(*y == c.rem_euclid(m)),
                                "M={m}, skip={skip}, r={r}, c={c}"
                            );
                            assert_eq!(images.answer(&Formula::negate(q), &def), Some(true));
                            checked += 2;
                        }
                    }
                }
            }
        }
        eprintln!("exact joint orbit checks={checked}");
    }
    #[test]
    fn monotone_clamp_images_match_independent_inverse_cuts() {
        let mut checked = 0;
        for a in [1i128, 2, 5, 7] {
            for b in [3i128, 7, 11] {
                if a == b {
                    continue;
                }
                for offset in [-9i128, 0, 4] {
                    for k in 1..=8 {
                        let basis = ClampBasis {
                            axis: Atom::Sym("x".into()),
                            a: Int::from(a),
                            b: Int::from(b),
                            constant: Int::from(offset),
                        };
                        let value = |x: i128| {
                            let bound = x.div_euclid(a) + x.div_euclid(b) + offset;
                            let mut h = x;
                            for _ in 0..k {
                                h = h.div_euclid(2).max(bound);
                            }
                            h
                        };
                        let cut = |c: i128| {
                            let mut lo = -1i128;
                            let mut hi = 1i128;
                            while value(lo) >= c {
                                lo *= 2;
                            }
                            while value(hi) < c {
                                hi *= 2;
                            }
                            while hi - lo > 1 {
                                let mid = (hi + lo).div_euclid(2);
                                if value(mid) >= c {
                                    hi = mid;
                                } else {
                                    lo = mid;
                                }
                            }
                            hi
                        };
                        for c in -30i128..=30 {
                            assert_eq!(
                                basis.contains(&Int::from(c), k),
                                cut(c) < cut(c + 1),
                                "a={a} b={b} C={offset} k={k} c={c}"
                            );
                            checked += 1;
                        }
                    }
                }
            }
        }
        eprintln!("two-quotient monotone-clamp image comparisons={checked}");
    }

    #[test]
    fn a_changed_modulus_requires_the_divisibility_guard() {
        let (mut defs, outputs) = chain(2, 1, false);
        let input = Lin::atom(outputs[0].clone());
        let n = defs.len() as u32;
        let q = Lin::atom(Atom::Aux(n));
        let r = Lin::atom(Atom::Aux(n + 1));
        let pair = Formula::And(Shared::new(vec![
            Formula::Con(Con::eq(&input, &q.times(3).plus(&r))),
            Formula::Con(Con::ge(&r, &Lin::constant(0))),
            Formula::Con(Con::ge(&Lin::constant(2), &r)),
        ]));
        defs.push(pair.clone());
        defs.push(pair);
        let output = Atom::Aux(n + 2);
        defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
            &Lin::atom(output.clone()),
            &input.plus(&r),
        ))])));
        let def = |n: u32| defs[n as usize].clone();
        let mut images = ScalarImages::default();
        for c in -12i64..=12 {
            let query = Formula::Con(Con::eq(&Lin::atom(output.clone()), &Lin::constant(c)));
            assert_eq!(images.answer(&query, &def), None);
            assert_eq!(
                decide_defined(&mut Summaries::default(), query, &def),
                Ok([0, 4, 5].contains(&c.rem_euclid(6)))
            );
        }
    }
    #[test]
    fn orbit_questions_keep_previous_and_future_residues_and_the_earlier_image() {
        let mut checked = 0;
        for m in [7i64, 1000, 1_000_000_007] {
            for skip in [false, true] {
                let (defs, outputs) = chain(m, 16, skip);
                let def = |n: u32| defs[n as usize].clone();
                let mut images = ScalarImages::default();
                let step = |h: i64| {
                    if skip {
                        h + if h.rem_euclid(m) == 0 { 1 } else { 2 }
                    } else {
                        h + h.rem_euclid(m)
                    }
                };
                for k in [0usize, 3, 7, 14] {
                    for c in [-1i64, 0, 2, 5, 6, 9] {
                        let mut pre = BTreeSet::from([c]);
                        for _ in 0..=k {
                            let mut next = BTreeSet::new();
                            for y in pre {
                                if skip {
                                    if (y - 1).rem_euclid(m) == 0 {
                                        next.insert(y - 1);
                                    }
                                    if (y - 2).rem_euclid(m) != 0 {
                                        next.insert(y - 2);
                                    }
                                } else {
                                    let q = y.div_euclid(m);
                                    for quotient in [q - 1, q] {
                                        let twice = y - m * quotient;
                                        if twice >= 0 && twice <= 2 * (m - 1) && twice % 2 == 0 {
                                            next.insert(m * quotient + twice / 2);
                                        }
                                    }
                                }
                            }
                            pre = next;
                        }
                        for j in [0usize, 2, 7, 14] {
                            for r in [0i64, 3, m - 1] {
                                let expected = pre.iter().any(|x| {
                                    let mut h = *x;
                                    for _ in 0..=j {
                                        h = step(h);
                                    }
                                    h.rem_euclid(m) == r
                                });
                                let remainder = Atom::Aux((3 * (j + 1) + 1) as u32);
                                let query = Formula::and(vec![
                                    Formula::Con(Con::eq(
                                        &Lin::atom(outputs[k].clone()),
                                        &Lin::constant(c),
                                    )),
                                    Formula::Con(Con::eq(&Lin::atom(remainder), &Lin::constant(r))),
                                ]);
                                assert_eq!(
                                    images.answer(&query, &def),
                                    Some(expected),
                                    "m={m} skip={skip} k={k} j={j} c={c} r={r}"
                                );
                                checked += 1;
                            }
                        }
                    }
                }
            }
        }
        for skip in [false, true] {
            let (defs, outputs) = chain(1000, 640, skip);
            let def = |n: u32| defs[n as usize].clone();
            let (c, r) = if skip { (1, 0) } else { (6, 3) };
            let query = Formula::and(vec![
                Formula::Con(Con::eq(&Lin::atom(outputs[639].clone()), &Lin::constant(c))),
                Formula::Con(Con::eq(
                    &Lin::atom(Atom::Aux(3 * 639 + 1)),
                    &Lin::constant(r),
                )),
            ]);
            assert_eq!(ScalarImages::default().answer(&query, &def), Some(false));
        }
        eprintln!("relative-period/earlier-image checks={checked}, plus two depth-640 exclusions");
    }
    #[test]
    fn scalar_images_keep_moduli_beyond_signed_i128_and_saturate_the_exponent() {
        let boundary = &Int::from(i128::MAX) + &Int::ONE;
        let mut checked = 0;
        for odd in [false, true] {
            let modulus = if odd {
                &boundary + &Int::ONE
            } else {
                boundary.clone()
            };
            let mut defs = Vec::new();
            let mut outputs = Vec::new();
            let mut input = Lin::atom(Atom::Sym("x".into()));
            for _ in 0..130 {
                let n = defs.len() as u32;
                let q = Lin::atom(Atom::Aux(n));
                let r = Lin::atom(Atom::Aux(n + 1));
                let pair = Formula::And(Shared::new(vec![
                    Formula::Con(Con::eq(&input, &q.times(modulus.clone()).plus(&r))),
                    Formula::Con(Con::ge(&r, &Lin::constant(0))),
                    Formula::Con(Con::ge(&Lin::constant(&modulus - &Int::ONE), &r)),
                ]));
                defs.push(pair.clone());
                defs.push(pair);
                let output = Atom::Aux(n + 2);
                defs.push(Formula::And(Shared::new(vec![Formula::Con(Con::eq(
                    &Lin::atom(output.clone()),
                    &input.plus(&r),
                ))])));
                input = Lin::atom(output.clone());
                outputs.push(output);
            }
            let def = |n: u32| defs[n as usize].clone();
            let mut images = ScalarImages::default();
            let mut divisor = Int::ONE;
            for (k, a) in outputs.iter().enumerate() {
                if k < 127 {
                    divisor = &divisor * &Int::from(2);
                }
                for c in [
                    Int::ZERO,
                    boundary.clone(),
                    -&boundary,
                    &boundary + &Int::ONE,
                    -&(&boundary + &Int::ONE),
                    &boundary + &Int::from(256),
                ] {
                    let query =
                        Formula::Con(Con::eq(&Lin::atom(a.clone()), &Lin::constant(c.clone())));
                    assert_eq!(
                        images.answer(&query, &def),
                        Some(odd || c.mod_floor(&divisor).is_zero()),
                        "odd={odd} k={k} c={c}"
                    );
                    checked += 1;
                }
            }
        }
        eprintln!("beyond-i128 scalar image checks={checked}, moduli 2^127 and 2^127+1, depth 130");
    }

    #[test]
    fn prefix_record_certificates_have_concrete_witnesses_for_signed_remainders() {
        fn pair(defs: &mut Vec<Formula>, arg: &Lin, m: i64) -> (Lin, Lin) {
            let n = defs.len() as u32;
            let q = Lin::atom(Atom::Aux(n));
            let r = Lin::atom(Atom::Aux(n + 1));
            let f = Formula::And(Shared::new(vec![
                Formula::Con(Con::eq(arg, &q.times(m).plus(&r))),
                Formula::Con(Con::ge(&r, &Lin::constant(0))),
                Formula::Con(Con::ge(&Lin::constant(m - 1), &r)),
            ]));
            defs.extend([f.clone(), f]);
            (q, r)
        }
        let mut checked = 0;
        for (m, d, w, c) in [
            (5i64, 7i64, 1i64, -9i64),
            (7, 7, -3, 4),
            (3, 11, 4, -2),
            (1, 1, 9, 0),
            (2, 3, -1, 0),
        ] {
            let mut defs = Vec::new();
            let x = Lin::atom(Atom::Sym("x".into()));
            let (_, r) = pair(&mut defs, &x, m);
            let (q, _) = pair(&mut defs, &x, d);
            let b = r.times(w).plus(&q).plus(&Lin::constant(c));
            let mut previous = x.clone();
            let mut outputs = Vec::new();
            for _ in 0..6 {
                let (half, _) = pair(&mut defs, &previous, 2);
                let out = Atom::Aux(defs.len() as u32);
                let guard = Formula::Con(Con::ge(&half, &b));
                let f = Formula::Or(Shared::new(vec![
                    Formula::and(vec![
                        guard.clone(),
                        Formula::Con(Con::eq(&Lin::atom(out.clone()), &half)),
                    ]),
                    Formula::and(vec![
                        Formula::negate(guard),
                        Formula::Con(Con::eq(&Lin::atom(out.clone()), &b)),
                    ]),
                ]));
                defs.push(f);
                previous = Lin::atom(out.clone());
                outputs.push(out);
            }
            let def = |n: u32| defs[n as usize].clone();
            let mut images = ScalarImages::default();
            let radius = d * (64 * (8 + c.abs() + 3) + w.abs() * (m - 1) + 3);
            let mut witnesses: Vec<BTreeSet<i64>> = vec![BTreeSet::new(); 6];
            for x in -radius..=radius {
                let bound = w * x.rem_euclid(m) + x.div_euclid(d) + c;
                let mut h = x;
                for ws in &mut witnesses {
                    h = h.div_euclid(2).max(bound);
                    if (-8..=8).contains(&h) {
                        ws.insert(h);
                    }
                }
            }
            for (k, out) in outputs.into_iter().enumerate() {
                for target in -8..=8 {
                    assert!(
                        witnesses[k].contains(&target),
                        "m={m},d={d},w={w},c={c},k={k},target={target}"
                    );
                    let query =
                        Formula::Con(Con::eq(&Lin::atom(out.clone()), &Lin::constant(target)));
                    assert_eq!(images.answer(&query, &def), Some(true));
                    checked += 1;
                }
            }
        }
        eprintln!(
            "prefix-record concrete witness checks={checked}, five signed/modulus configurations, depth 6"
        );
    }

    #[test]
    fn a_condition_cannot_combine_independent_scalar_images_into_a_joint_image() {
        let x = Lin::atom(Atom::Sym("x".into()));
        let out = Lin::atom(Atom::Aux(0));
        let guard = Formula::Con(Con::ge(&x, &Lin::constant(0)));
        let f = Formula::Or(Shared::new(vec![
            Formula::and(vec![
                guard.clone(),
                Formula::Con(Con::eq(&out, &x.plus(&Lin::constant(100)))),
            ]),
            Formula::and(vec![
                Formula::negate(guard),
                Formula::Con(Con::eq(&out, &x)),
            ]),
        ]));
        let def = |_| f.clone();
        let mut images = ScalarImages::default();
        for c in [9i64, -1, 100] {
            let query = Formula::Con(Con::eq(&out, &Lin::constant(c)));
            let scalar = images.answer(&query, &def);
            if let Some(answer) = scalar {
                assert_eq!(
                    answer,
                    c < 0 || c >= 100,
                    "an accepted certificate must be exact"
                );
            }
            assert_eq!(scalar, None);
            assert_eq!(
                decide_defined(&mut Summaries::default(), query, &def),
                Ok(c < 0 || c >= 100)
            );
        }
    }
}
