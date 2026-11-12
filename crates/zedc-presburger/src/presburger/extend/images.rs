//! Exact scalar images and translation-period orbits. Scalar certificates read one
//! value; the orbit certificate additionally retains its original input remainder.
//! Other joint questions continue to use the relational summaries with all their inputs.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use super::super::formula::{Atom, Con, Formula, Id, Lin, Rel};
use super::def::{Def, free, reads};
use zedc_int::int::Int;
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
                    || (!r.is_zero() && (&Int::from(2) * k) < r)
                    || (r.is_zero() && !m.is_odd() && (&Int::from(2) * k) < **m)
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
mod tests;
