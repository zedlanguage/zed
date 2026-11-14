//! The graph families of cross-review X14 (xs), by which its deciders were measured: each
//! generator copied without change from the cross-measure (wt/xs-cmp/src: claude.rs, codex.rs,
//! gemini.rs, claude/codex_r1.rs), with one graph type for all, and the widening of a node
//! (wt/xs-cmp/src/main.rs `widen_kind`).

use zed_kernel::types::bes::{Bes, Kind};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum K {
    Or,
    And,
    Mor,
    Top,
    Bot,
}

#[derive(Clone, Debug, Default)]
pub struct G {
    pub k: Vec<K>,
    pub c: Vec<Vec<u32>>,
    pub p: Vec<Vec<u32>>,
}

impl G {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn add(&mut self, k: K, c: Vec<u32>) -> u32 {
        self.k.push(k);
        self.c.push(c);
        self.p.push(vec![]);
        (self.k.len() - 1) as u32
    }
    pub fn seal(&mut self) {
        for v in 0..self.k.len() {
            self.p[v].clear();
        }
        for v in 0..self.k.len() {
            for i in 0..self.c[v].len() {
                let w = self.c[v][i] as usize;
                self.p[w].push(v as u32);
            }
        }
    }
    pub fn n(&self) -> usize {
        self.k.len()
    }

    /// The system the kernel decides.
    pub fn bes(&self) -> Bes {
        let mut b = Bes::new();
        for v in 0..self.k.len() {
            let k = match self.k[v] {
                K::Or => Kind::Or,
                K::And => Kind::And,
                K::Mor => Kind::Mor,
                K::Top => Kind::Top,
                K::Bot => Kind::Bot,
            };
            b.add(k, self.c[v].clone());
        }
        b.seal();
        b
    }
}

mod claude {
    use super::*;
    fn rnd(x: &mut u64) -> u64 {
        *x ^= *x << 13;
        *x ^= *x >> 7;
        *x ^= *x << 17;
        *x
    }

    pub(super) fn random(x: &mut u64, n: usize, pmor: u64) -> G {
        let mut g = G::default();
        for _ in 0..n {
            let r = rnd(x) % 20;
            let k = if r == 0 {
                K::Bot
            } else if r == 1 {
                K::Top
            } else if r < 20 - pmor {
                if r.is_multiple_of(2) { K::Or } else { K::And }
            } else {
                K::Mor
            };
            g.add(k, vec![]);
        }
        for v in 0..n {
            let d = match g.k[v] {
                K::Mor => 1,
                K::Or | K::And => 1 + rnd(x) % 3,
                _ => 0,
            };
            for _ in 0..d {
                let w = (rnd(x) % n as u64) as u32;
                g.c[v].push(w);
            }
        }
        g.seal();
        g
    }

    /// T_i = (int)->V_i, V_i = (T_{i+1}, T_i), V_n = (T_n, bad)
    pub(super) fn chain(n: usize) -> G {
        let mut g = G::default();
        let bad = g.add(K::Bot, vec![]);
        let t: Vec<u32> = (0..=n).map(|_| g.add(K::Mor, vec![])).collect();
        let v: Vec<u32> = (0..=n)
            .map(|i| {
                g.add(
                    K::And,
                    if i == n {
                        vec![t[i], bad]
                    } else {
                        vec![t[i + 1], t[i]]
                    },
                )
            })
            .collect();
        for i in 0..=n {
            g.c[t[i] as usize] = vec![v[i]];
        }
        g.seal();
        g
    }

    /// L_i = A_i | Z_i, A_i = (L_i, ...), Z_i = (int)->L_{i+1}; `big` joins all into one tuple component.
    fn ladder_into(g: &mut G, n: usize, big: bool) -> Vec<u32> {
        let top = g.add(K::Top, vec![]);
        let l: Vec<u32> = (0..n).map(|_| g.add(K::Or, vec![])).collect();
        let mut ors = vec![];
        if big {
            for i in 0..n {
                let a = if i + 1 < n { l[i + 1] } else { l[0] };
                let b = l[(i + n - 1) % n];
                ors.push((g.add(K::Or, vec![a, top]), g.add(K::Or, vec![b, top])));
            }
        }
        for i in 0..n {
            let mut cc = vec![l[i]];
            if big {
                cc.push(ors[i].0);
                cc.push(ors[i].1);
            }
            let a = g.add(K::And, cc);
            let mut alt = vec![a];
            if i + 1 < n {
                alt.push(g.add(K::Mor, vec![l[i + 1]]));
            }
            g.c[l[i] as usize] = alt;
        }
        l
    }

    pub(super) fn ladder(n: usize, big: bool) -> G {
        let mut g = G::default();
        ladder_into(&mut g, n, big);
        g.seal();
        g
    }

    /// A ladder kills L_{n-1}, L_{n-2}, ... one per round; s_k = (int)->L_{n-1-k} dies in round k.
    /// C_k = left | C_{k+1} | s_k with left = C_{k-1} (flip) or (C_{k-1}, top) (flipand).
    pub(super) fn flip(n: usize, and: bool) -> G {
        let mut g = G::default();
        let l = ladder_into(&mut g, n, false);
        let top = g.add(K::Top, vec![]);
        let s: Vec<u32> = (0..n).map(|k| g.add(K::Mor, vec![l[n - 1 - k]])).collect();
        let c: Vec<u32> = (0..n).map(|_| g.add(K::Or, vec![])).collect();
        for k in 0..n {
            let mut ch = vec![];
            if k > 0 {
                ch.push(if and {
                    g.add(K::And, vec![c[k - 1], top])
                } else {
                    c[k - 1]
                });
            }
            if k + 1 < n {
                ch.push(c[k + 1]);
            }
            ch.push(s[k]);
            g.c[c[k] as usize] = ch;
        }
        g.seal();
        g
    }

    /// Built to defeat split: L_i = (L_i, P_i) | (int)->L_{i+1}, P_i = L_{i-1} | L_{i+1}. Unlike
    /// bigladder, P_i has no constant alternative, so the bounds leave one alternating component.
    pub(super) fn hardladder(n: usize) -> G {
        let mut g = G::default();
        let l: Vec<u32> = (0..n).map(|_| g.add(K::Or, vec![])).collect();
        for i in 0..n {
            let p = g.add(K::Or, vec![l[(i + n - 1) % n], l[(i + 1) % n]]);
            let a = g.add(K::And, vec![l[i], p]);
            let mut alt = vec![a];
            if i + 1 < n {
                alt.push(g.add(K::Mor, vec![l[i + 1]]));
            }
            g.c[l[i] as usize] = alt;
        }
        g.seal();
        g
    }

    /// hardladder as the timer of flipand, with P_i = L_{i-1} | L_{i+1} | C_i, so the chain and the
    /// timer form one alternating component: refused by split and quadratic for justify.
    pub(super) fn hardflip(n: usize) -> G {
        let mut g = G::default();
        let top = g.add(K::Top, vec![]);
        let l: Vec<u32> = (0..n).map(|_| g.add(K::Or, vec![])).collect();
        let c: Vec<u32> = (0..n).map(|_| g.add(K::Or, vec![])).collect();
        for i in 0..n {
            let p = g.add(K::Or, vec![l[(i + n - 1) % n], l[(i + 1) % n], c[i]]);
            let a = g.add(K::And, vec![l[i], p]);
            let mut alt = vec![a];
            if i + 1 < n {
                alt.push(g.add(K::Mor, vec![l[i + 1]]));
            }
            g.c[l[i] as usize] = alt;
        }
        let s: Vec<u32> = (0..n).map(|k| g.add(K::Mor, vec![l[n - 1 - k]])).collect();
        for k in 0..n {
            let mut ch = vec![];
            if k > 0 {
                ch.push(g.add(K::And, vec![c[k - 1], top]));
            }
            if k + 1 < n {
                ch.push(c[k + 1]);
            }
            ch.push(s[k]);
            g.c[c[k] as usize] = ch;
        }
        g.seal();
        g
    }

    /// n copies of a small system, one full SCC each, joined in a ring: child `slot` of node `from`
    /// in copy i points to its node in copy i + 1 (mod n) instead.
    fn ring(n: usize, gadget: &[(K, &[u32])], from: usize, slot: usize) -> G {
        let k = gadget.len() as u32;
        let mut g = G::default();
        for i in 0..n as u32 {
            for (v, (kind, cs)) in gadget.iter().enumerate() {
                let next = (i + 1) % n as u32;
                let c = cs
                    .iter()
                    .enumerate()
                    .map(|(j, &w)| {
                        if v == from && j == slot {
                            next * k + w
                        } else {
                            i * k + w
                        }
                    })
                    .collect();
                g.add(*kind, c);
            }
        }
        g.seal();
        g
    }

    /// Ring of the smallest system that splitC refuses and splitD decides by the existential case:
    /// `0:Mor[1] 1:Or[1,2] 2:Or[0,1]` (found by `xs2 gadget exist`).
    pub(super) fn exring(n: usize) -> G {
        ring(
            n,
            &[(K::Mor, &[1]), (K::Or, &[1, 2]), (K::Or, &[0, 1])],
            2,
            0,
        )
    }

    /// exring with every Or replaced by And: the universal counterpart.
    pub(super) fn unring(n: usize) -> G {
        ring(
            n,
            &[(K::Mor, &[1]), (K::And, &[1, 2]), (K::And, &[0, 1])],
            2,
            0,
        )
    }

    /// Ring of the smallest system that splitD refuses (two players, two Mor nodes, from `xs2 cmp`):
    /// `0:And[1,2] 1:Mor[3] 2:Or[3,0,3] 3:Mor[0]`. Built to make splitD refuse everything.
    pub(super) fn defeat_d(n: usize) -> G {
        ring(
            n,
            &[
                (K::And, &[1, 2]),
                (K::Mor, &[3]),
                (K::Or, &[3, 0, 3]),
                (K::Mor, &[0]),
            ],
            3,
            0,
        )
    }

    /// Built to defeat splitD+gsr: a defeatD ring (refused by splitD) and an unring ring (quadratic
    /// for Gemini at lib.rs:1958) joined into one SCC through J = Or[defeatD 0, unring 0], a child of
    /// defeatD node 2 and of unring node 2 in copy 0. J is true, so no value changes; gsr must solve
    /// the whole SCC, unring part included.
    pub(super) fn defeat_gsr(n: usize) -> G {
        let mut g = defeat_d(n);
        let base = g.n() as u32;
        let u = unring(n);
        for v in 0..u.n() {
            let c = u.c[v].iter().map(|&w| w + base).collect();
            g.add(u.k[v], c);
        }
        let j = g.add(K::Or, vec![0, base]);
        g.c[2].push(j);
        g.c[base as usize + 2].push(j);
        g.seal();
        g
    }
}

mod codex {
    use super::*;
    pub(super) fn tiles(n: usize) -> G {
        let mut g = G::default();
        for _ in 0..n {
            let r = g.add(K::Or, vec![]);
            let a = g.add(K::And, vec![r, r + 2]);
            let s = g.add(K::Or, vec![r, a]);
            g.c[r as usize] = vec![a, s];
        }
        g.seal();
        g
    }
    pub(super) fn codex_adversary(n: usize) -> G {
        let mut g = G::default();
        let top = g.add(K::Top, vec![]);
        let l: Vec<_> = (0..n).map(|_| g.add(K::Or, vec![])).collect();
        for i in 0..n {
            let x = g.add(K::Or, vec![l[(i + 1) % n], l[(i + n - 1) % n]]);
            let y = g.add(K::Or, vec![l[(i + n - 1) % n], top]);
            let t = g.add(K::And, vec![l[i], x, y]);
            let mut alt = vec![t];
            if i + 1 < n {
                alt.push(g.add(K::Mor, vec![l[i + 1]]));
            }
            g.c[l[i] as usize] = alt;
        }
        g.seal();
        g
    }
    pub(super) fn guard_unions(mut g: G) -> G {
        let count = g.n();
        for v in 0..count {
            if g.k[v] == K::Or {
                let old = std::mem::take(&mut g.c[v]);
                for w in old {
                    let a = g.add(K::And, vec![w]);
                    g.c[v].push(a);
                }
            }
        }
        g.seal();
        g
    }
}

mod gemini {
    use super::*;
    pub fn chain(n: usize) -> G {
        let mut g = G::new();
        let bad = g.add(K::Bot, Vec::new());
        let t: Vec<u32> = (0..=n).map(|_| g.add(K::Mor, Vec::new())).collect();
        let v: Vec<u32> = (0..=n)
            .map(|i| {
                g.add(
                    K::And,
                    if i == n {
                        vec![t[i], bad]
                    } else {
                        vec![t[i + 1], t[i]]
                    },
                )
            })
            .collect();
        for i in 0..=n {
            g.c[t[i] as usize] = vec![v[i]];
        }
        g.seal();
        g
    }

    /// `ladder(n, big)` from `Q2Q3/bes`: `big = false` has n 2-node tuple SCCs;
    /// `big = true` (`bigladder`) links all n rungs into one 4n-node static tuple SCC via `Or(..., Top)`.
    pub fn ladder(n: usize, big: bool) -> G {
        let mut g = G::new();
        let top = g.add(K::Top, Vec::new());
        let l: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        let mut ors = Vec::new();
        if big {
            for i in 0..n {
                let a = if i + 1 < n { l[i + 1] } else { l[0] };
                let b = l[(i + n - 1) % n];
                ors.push((g.add(K::Or, vec![a, top]), g.add(K::Or, vec![b, top])));
            }
        }
        for i in 0..n {
            let mut cc = vec![l[i]];
            if big {
                cc.push(ors[i].0);
                cc.push(ors[i].1);
            }
            let a = g.add(K::And, cc);
            let mut alt = vec![a];
            if i + 1 < n {
                alt.push(g.add(K::Mor, vec![l[i + 1]]));
            }
            g.c[l[i] as usize] = alt;
        }
        g.seal();
        g
    }

    /// Adversarial family `adv_bigladder_mor(n)`: replaces `top` in `bigladder(n)` with a coinductive
    /// `Mor` cycle `m_coind = Mor(m_coind)`, so `ors[i]` is NOT in `G_top = \mu L. F(\emptyset, L)`.
    /// Tests that `dw_delcheck` and `bdw_delcheck` still solve it in O(n) via witness-edge filtering!
    pub fn adv_bigladder_mor(n: usize) -> G {
        let mut g = G::new();
        let m_coind = g.add(K::Mor, Vec::new());
        g.c[m_coind as usize] = vec![m_coind];
        let l: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        let mut ors = Vec::new();
        for i in 0..n {
            let a = if i + 1 < n { l[i + 1] } else { l[0] };
            let b = l[(i + n - 1) % n];
            ors.push((
                g.add(K::Or, vec![a, m_coind]),
                g.add(K::Or, vec![b, m_coind]),
            ));
        }
        for i in 0..n {
            let cc = vec![l[i], ors[i].0, ors[i].1];
            let a = g.add(K::And, cc);
            let mut alt = vec![a];
            if i + 1 < n {
                alt.push(g.add(K::Mor, vec![l[i + 1]]));
            }
            g.c[l[i] as usize] = alt;
        }
        g.seal();
        g
    }

    /// Builds a sequential `n`-round `Mor` timer chain: `m_chain[r]` dies in round `r + 1` (`r = 0..n`).
    /// Each step is gated by a 2-node ungrounded tuple cycle `tl[r] <-> ta[r]`, matching `ladder(n, false)`.
    fn build_mor_timer_chain(g: &mut G, n: usize) -> Vec<u32> {
        let tl: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        let mut m_chain = Vec::with_capacity(n);
        for r in 0..n {
            let ta = g.add(K::And, vec![tl[r]]);
            let mut alt = vec![ta];
            if r > 0 {
                alt.push(m_chain[r - 1]);
            }
            g.c[tl[r] as usize] = alt;
            m_chain.push(g.add(K::Mor, vec![tl[r]]));
        }
        m_chain
    }

    /// Adversarial family `reanchor_ring(n)`:
    /// A single ungrounded cycle `R_0 -> A_0 -> R_1 -> A_1 -> ... -> R_{n-1} -> A_{n-1} -> R_0`
    /// where each `R_i = Or(A_i, m_i)` has an external `Mor` seed `m_i` that dies in round `i + 1`.
    /// Defeats `delcheck`, `ch12_hl`, and `dw_delcheck` (`\Theta(n^2)` work across `n` rounds),
    /// while `bdw_delcheck` and `sr_bdw_delcheck` solve it in O(n) linear time via Rule B!
    pub fn reanchor_ring(n: usize) -> G {
        let mut g = G::new();
        let top = g.add(K::Top, Vec::new());
        let m_chain = build_mor_timer_chain(&mut g, n);
        let r: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        let a: Vec<u32> = (0..n)
            .map(|i| g.add(K::And, vec![r[(i + 1) % n], top]))
            .collect();
        for i in 0..n {
            g.c[r[i] as usize] = vec![a[i], m_chain[i]];
        }
        g.seal();
        g
    }

    /// Adversarial family `reanchor_cut_ring(n)`:
    /// Same ring as `reanchor_ring(n)`, except `A_{n-1} = And(R_0, m_chain[0])` dies in Round 1,
    /// cutting the ring into an acyclic path of `2n - 1` nodes while `m_chain[1..n]` die in rounds `2..=n`.
    /// Defeats `delcheck` and `ch12_hl` (`\Theta(n^2)` static-SCC work), while `bdw_delcheck` and
    /// `sr_bdw_delcheck` promote the cut ring to `in_dag` (Rule A) in Round 1 and solve it in O(n) time!
    pub fn reanchor_cut_ring(n: usize) -> G {
        let mut g = G::new();
        let top = g.add(K::Top, Vec::new());
        let m_chain = build_mor_timer_chain(&mut g, n);
        let r: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        let a: Vec<u32> = (0..n)
            .map(|i| {
                let blocker = if i + 1 == n { m_chain[0] } else { top };
                g.add(K::And, vec![r[(i + 1) % n], blocker])
            })
            .collect();
        for i in 0..n {
            g.c[r[i] as usize] = vec![a[i], m_chain[i]];
        }
        g.seal();
        g
    }

    /// Adversarial family `bidir_trap(n)`:
    /// A genuine 2-player Alternating Buchi Game embedded inside a single ungrounded tuple SCC `C`:
    /// - `R_i = Or([A_i, R_{(i+1)%n}, m_chain[i]])`
    /// - `P_i = Or([R_i, P_{(i+1)%n}])`
    /// - `A_i = And([R_{(i+1)%n}, P_{(i+n-1)%n}, m_chain[i]])`
    ///
    /// Forces `\Theta(n^2)` work in all non-refusing solvers (`delcheck`, `dw_delcheck`, `bdw_delcheck`),
    /// and is caught statically in O(n) time by `sr_bdw_delcheck` (`SR-AMC`) and `split_bdw`!
    pub fn bidir_trap(n: usize) -> G {
        let mut g = G::new();
        let m_chain = build_mor_timer_chain(&mut g, n);
        let r: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        let p: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        let a: Vec<u32> = (0..n)
            .map(|i| g.add(K::And, vec![r[(i + 1) % n], p[(i + n - 1) % n], m_chain[i]]))
            .collect();
        for i in 0..n {
            g.c[r[i] as usize] = vec![a[i], r[(i + 1) % n], m_chain[i]];
            g.c[p[i] as usize] = vec![r[i], p[(i + 1) % n]];
        }
        g.seal();
        g
    }

    /// Codex `cyclic_ladder(n)` from `peers/codex/prototype/src/lib.rs:582-607`:
    /// `l_i = Or(And(l_i, l_{i+1}, l_{i-1}), Mor(l_{i+1}))` (with `l_{n-1}` having no `Mor` arm).
    /// Notice the tuple ring has no `Top` child, so `lo` and `hi` decide it as `Empty` in Step 1!
    pub fn cyclic_ladder(n: usize) -> G {
        let mut g = G::new();
        let l: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        for i in 0..n {
            let next = if i + 1 < n { l[i + 1] } else { l[0] };
            let prev = l[(i + n - 1) % n];
            let a = g.add(K::And, vec![l[i], next, prev]);
            let mut alt = vec![a];
            if i + 1 < n {
                alt.push(g.add(K::Mor, vec![l[i + 1]]));
            }
            g.c[l[i] as usize] = alt;
        }
        g.seal();
        g
    }

    /// Codex `adversary(n)` from `peers/codex/prototype/src/lib.rs:609-646`:
    /// Bidirectional `Or` ring coupled with `And(l_i, r_i, u_i)` and `Mor(l_{i+1})`.
    pub fn codex_adversary(n: usize) -> G {
        let mut g = G::new();
        let l: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        let u: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        let r: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        let m: Vec<u32> = (0..n.saturating_sub(1))
            .map(|i| g.add(K::Mor, vec![l[i + 1]]))
            .collect();
        let a: Vec<u32> = (0..n)
            .map(|i| g.add(K::And, vec![l[i], r[i], u[i]]))
            .collect();
        for i in 0..n {
            let mut u_ch = vec![l[i]];
            if i > 0 {
                u_ch.push(u[i - 1]);
            }
            if i + 1 < n {
                u_ch.push(u[i + 1]);
            }
            g.c[u[i] as usize] = u_ch;

            let mut r_ch = vec![u[i]];
            if i + 1 < n {
                r_ch.push(m[i]);
            }
            g.c[r[i] as usize] = r_ch;

            let mut l_ch = vec![a[i]];
            if i + 1 < n {
                l_ch.push(m[i]);
            }
            g.c[l[i] as usize] = l_ch;
        }
        g.seal();
        g
    }

    fn claude_flip_impl(n: usize, and: bool) -> G {
        let mut g = G::new();
        let top = g.add(K::Top, Vec::new());
        let l: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        for i in 0..n {
            let a = g.add(K::And, vec![l[i]]);
            let mut alt = vec![a];
            if i + 1 < n {
                alt.push(g.add(K::Mor, vec![l[i + 1]]));
            }
            g.c[l[i] as usize] = alt;
        }
        let s: Vec<u32> = (0..n).map(|k| g.add(K::Mor, vec![l[n - 1 - k]])).collect();
        let c: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        for k in 0..n {
            let mut ch = Vec::new();
            if k > 0 {
                ch.push(if and {
                    g.add(K::And, vec![c[k - 1], top])
                } else {
                    c[k - 1]
                });
            }
            if k + 1 < n {
                ch.push(c[k + 1]);
            }
            ch.push(s[k]);
            g.c[c[k] as usize] = ch;
        }
        g.seal();
        g
    }

    /// Claude `flip(n)` from `peers/claude/xs/src/main.rs:1297-1320` (`and = false`):
    /// A ladder kills `L_{n-1}, ..., L_0` one per round; `s_k = Mor(L_{n-1-k})` dies in round `k`;
    /// `C_k = C_{k-1} | C_{k+1} | s_k`.
    pub fn claude_flip(n: usize) -> G {
        claude_flip_impl(n, false)
    }

    /// Claude `flipand(n)` from `peers/claude/xs/src/main.rs:1297-1320` (`and = true`):
    /// Same as `flip(n)`, with `left = And(C_{k-1}, top)`.
    /// Refused by Claude's `splitC`, but solved in 1 pass (`O(n)` time) by `split_bdw`!
    pub fn claude_flipand(n: usize) -> G {
        claude_flip_impl(n, true)
    }

    /// Claude `hardladder(n)` from `peers/claude/xs/src/main.rs:1324-1338`:
    /// `L_i = (L_i, P_i) | () -> L_{i+1}`, `P_i = L_{i-1} | L_{i+1}`.
    pub fn claude_hardladder(n: usize) -> G {
        let mut g = G::new();
        let l: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        for i in 0..n {
            let p = g.add(K::Or, vec![l[(i + n - 1) % n], l[(i + 1) % n]]);
            let a = g.add(K::And, vec![l[i], p]);
            let mut alt = vec![a];
            if i + 1 < n {
                alt.push(g.add(K::Mor, vec![l[i + 1]]));
            }
            g.c[l[i] as usize] = alt;
        }
        g.seal();
        g
    }

    /// Claude `hardflip(n)` from `peers/claude/xs/src/main.rs:1342-1370`:
    /// `hardladder` as the timer of `flipand`, with `P_i = L_{i-1} | L_{i+1} | C_i`.
    pub fn claude_hardflip(n: usize) -> G {
        let mut g = G::new();
        let top = g.add(K::Top, Vec::new());
        let l: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        let c: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        for i in 0..n {
            let p = g.add(K::Or, vec![l[(i + n - 1) % n], l[(i + 1) % n], c[i]]);
            let a = g.add(K::And, vec![l[i], p]);
            let mut alt = vec![a];
            if i + 1 < n {
                alt.push(g.add(K::Mor, vec![l[i + 1]]));
            }
            g.c[l[i] as usize] = alt;
        }
        let s: Vec<u32> = (0..n).map(|k| g.add(K::Mor, vec![l[n - 1 - k]])).collect();
        for k in 0..n {
            let mut ch = Vec::new();
            if k > 0 {
                ch.push(g.add(K::And, vec![c[k - 1], top]));
            }
            if k + 1 < n {
                ch.push(c[k + 1]);
            }
            ch.push(s[k]);
            g.c[c[k] as usize] = ch;
        }
        g.seal();
        g
    }

    /// Round 2 adversarial family `indirect_alt_ladder(n)` built to test `split_bdw`'s refusal path:
    /// Uses length-3 indirect cycles `L_i -> a_i -> Q_i -> L_i` (`Q_i = L_i | L_{i+1}`, `P_i = L_{i-1} | L_{i+1}`,
    /// `a_i = And(Q_i, P_i)`) so `L_i` is not a direct child of `a_i`.
    /// Forces `\Theta(n^2)` work in `delcheck` and `bdw_delcheck`, and is refused in `O(n)` time by `split_bdw`.
    pub fn indirect_alt_ladder(n: usize) -> G {
        let mut g = G::new();
        let top = g.add(K::Top, Vec::new());
        let l: Vec<u32> = (0..n).map(|_| g.add(K::Or, Vec::new())).collect();
        for i in 0..n {
            let q = g.add(K::And, vec![l[i], top]);
            let p = g.add(K::Or, vec![l[(i + n - 1) % n], l[(i + 1) % n]]);
            let a = g.add(K::And, vec![q, p]);
            let mut alt = vec![a];
            if i + 1 < n {
                alt.push(g.add(K::Mor, vec![l[i + 1]]));
            }
            g.c[l[i] as usize] = alt;
        }
        g.seal();
        g
    }
}

mod codex_r1 {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub(crate) enum Kind {
        Or,
        And,
        Mor,
        Top,
        Bot,
    }
    #[derive(Clone, Debug)]
    pub(crate) struct Graph {
        kind: Vec<Kind>,
        child: Vec<Vec<usize>>,
        parent: Vec<Vec<usize>>,
    }
    impl Graph {
        fn new() -> Self {
            Self {
                kind: vec![],
                child: vec![],
                parent: vec![],
            }
        }
        fn add(&mut self, kind: Kind, child: Vec<usize>) -> usize {
            let id = self.kind.len();
            self.kind.push(kind);
            self.child.push(child);
            self.parent.push(vec![]);
            id
        }
        fn seal(&mut self) {
            self.parent = vec![vec![]; self.kind.len()];
            for (v, children) in self.child.iter().enumerate() {
                for &w in children {
                    self.parent[w].push(v);
                }
            }
        }
    }
    /// The Codex family generator (chain, ladder, bigladder, adversary) in this crate's graph.
    pub(super) fn family_g(name: &str, n: usize) -> super::G {
        let h = family(name, n);
        let mut g = super::G::default();
        for v in 0..h.kind.len() {
            let k = match h.kind[v] {
                Kind::Or => super::K::Or,
                Kind::And => super::K::And,
                Kind::Mor => super::K::Mor,
                Kind::Top => super::K::Top,
                Kind::Bot => super::K::Bot,
            };
            g.add(k, h.child[v].iter().map(|&w| w as u32).collect());
        }
        g.seal();
        g
    }
    pub(crate) fn family(name: &str, n: usize) -> Graph {
        let mut g = Graph::new();
        if name == "chain" {
            let bot = g.add(Kind::Bot, vec![]);
            let t: Vec<_> = (0..=n).map(|_| g.add(Kind::Mor, vec![])).collect();
            for i in 0..=n {
                let a = g.add(Kind::And, vec![t[i], if i == n { bot } else { t[i + 1] }]);
                g.child[t[i]] = vec![a];
            }
        } else {
            let top = g.add(Kind::Top, vec![]);
            let l: Vec<_> = (0..n).map(|_| g.add(Kind::Or, vec![])).collect();
            for i in 0..n {
                let mut parts = vec![l[i]];
                if name == "bigladder" || name == "adversary" {
                    let a = g.add(
                        Kind::Or,
                        vec![
                            l[(i + 1) % n],
                            if name == "adversary" {
                                l[(i + n - 1) % n]
                            } else {
                                top
                            },
                        ],
                    );
                    let b = g.add(Kind::Or, vec![l[(i + n - 1) % n], top]);
                    parts.extend([a, b]);
                }
                let a = g.add(Kind::And, parts);
                let mut alts = vec![a];
                if i + 1 < n {
                    alts.push(g.add(Kind::Mor, vec![l[i + 1]]));
                }
                g.child[l[i]] = alts;
            }
        }
        g.seal();
        g
    }
}

/// The 35 families measured.
pub const FAMILIES: [&str; 35] = [
    "chain",
    "ladder",
    "bigladder",
    "flip",
    "flipand",
    "hardladder",
    "hardflip",
    "g_chain",
    "g_ladder",
    "g_bigladder",
    "adv_bigladder_mor",
    "reanchor_ring",
    "reanchor_cut_ring",
    "bidir_trap",
    "c_chain",
    "c_ladder",
    "c_bigladder",
    "c_adversary",
    "exring",
    "unring",
    "defeatD",
    "defeatgsr",
    "codex_adversary",
    "mu_bidir",
    "guarded_mu_bidir",
    "random",
    "tiles",
    "cut_tiles",
    "cyclic_ladder",
    "claude_flip",
    "claude_flipand",
    "g_codex_adversary",
    "claude_hardladder",
    "claude_hardflip",
    "indirect_alt_ladder",
];

fn relabel_mor_to_or(mut g: G) -> G {
    for k in &mut g.k {
        if *k == K::Mor {
            *k = K::Or;
        }
    }
    g
}

/// Disjoint union of `copies` copies of `x`.
fn tile(x: &G, copies: usize) -> G {
    let m = x.k.len() as u32;
    let mut y = G::new();
    for i in 0..copies as u32 {
        y.k.extend_from_slice(&x.k);
        y.c.extend(
            x.c.iter()
                .map(|ch| ch.iter().map(|&w| w + i * m).collect::<Vec<_>>()),
        );
    }
    y.p = vec![vec![]; y.k.len()];
    y.seal();
    y
}

/// Node `v` widened by `wide` new children in place of its first child `w`: relays of `v`'s
/// kind (`same`) or of the kind named to `w`.
fn widen(x: &G, v: usize, wide: usize, kind: &str) -> G {
    let mut y = x.clone();
    let w = y.c[v][0];
    let mut kids: Vec<u32> = vec![];
    for _ in 0..wide {
        let k = match kind {
            "same" => x.k[v],
            "or" => K::Or,
            "and" => K::And,
            "mor" => K::Mor,
            _ => panic!("widen kind {kind}"),
        };
        kids.push(y.add(k, vec![w]));
    }
    kids.extend_from_slice(&x.c[v][1..]);
    y.c[v] = kids;
    y.seal();
    y
}

/// A random system of `n` nodes from `seed`: about `rate` in 20 nodes are morphisms, one in 20
/// `Top`, one in 20 `Bot`, and the rest `Or` and `And` nodes of one to three children. Family
/// `random` is seed `0x2545_F491_4F6C_DD1D` at rate 5. The generator is a xorshift, which
/// stays at 0 from 0, so seed 0 is read as that seed.
pub fn random(seed: u64, rate: u64, n: usize) -> G {
    assert!(rate <= 18, "at most 18 in 20 nodes are morphisms");
    let mut x = if seed == 0 {
        0x2545_F491_4F6C_DD1D
    } else {
        seed
    };
    claude::random(&mut x, n, rate)
}

/// Family `f` at size `n`; `BASE:BASEN:NODE[:KIND]` is family `BASE` at size `BASEN` with node
/// `NODE` widened by `n` children.
pub fn family(f: &str, n: usize) -> G {
    let p: Vec<&str> = f.split(':').collect();
    if let [base, bn, node, rest @ ..] = &p[..] {
        let kind = rest.first().copied().unwrap_or("same");
        let g = family(base, bn.parse().expect("base size"));
        return widen(&g, node.parse().expect("node"), n, kind);
    }
    match f {
        "chain" => claude::chain(n),
        "ladder" => claude::ladder(n, false),
        "bigladder" => claude::ladder(n, true),
        "flip" => claude::flip(n, false),
        "flipand" => claude::flip(n, true),
        "hardladder" => claude::hardladder(n),
        "hardflip" => claude::hardflip(n),
        "exring" => claude::exring(n),
        "unring" => claude::unring(n),
        "defeatD" => claude::defeat_d(n),
        "defeatgsr" => claude::defeat_gsr(n),
        "random" => claude::random(&mut 0x2545_F491_4F6C_DD1D, n, 5),
        "c_chain" | "c_ladder" | "c_bigladder" | "c_adversary" => {
            codex_r1::family_g(f.trim_start_matches("c_"), n)
        }
        "codex_adversary" => codex::codex_adversary(n),
        "tiles" => codex::tiles(n),
        "g_chain" => gemini::chain(n),
        "g_ladder" => gemini::ladder(n, false),
        "g_bigladder" => gemini::ladder(n, true),
        "cyclic_ladder" => gemini::cyclic_ladder(n),
        "adv_bigladder_mor" => gemini::adv_bigladder_mor(n),
        "reanchor_ring" => gemini::reanchor_ring(n),
        "reanchor_cut_ring" => gemini::reanchor_cut_ring(n),
        "claude_flip" => gemini::claude_flip(n),
        "claude_flipand" => gemini::claude_flipand(n),
        "bidir_trap" => gemini::bidir_trap(n),
        "g_codex_adversary" => gemini::codex_adversary(n),
        "claude_hardladder" => gemini::claude_hardladder(n),
        "claude_hardflip" => gemini::claude_hardflip(n),
        "indirect_alt_ladder" => gemini::indirect_alt_ladder(n),
        "mu_bidir" => relabel_mor_to_or(gemini::bidir_trap(n)),
        "guarded_mu_bidir" => codex::guard_unions(relabel_mor_to_or(gemini::bidir_trap(n))),
        "cut_tiles" => tile(&gemini::reanchor_cut_ring(3), n),
        _ => panic!("family {f}"),
    }
}

/// The classical Büchi game reference (McNaughton and Zielonka iteration, O(n m)), copied from
/// the cross-measure (claude.rs): the answer every decided node must match.
pub mod reference {
    use super::*;
    struct Game {
        p2: Vec<bool>,
        buchi: Vec<bool>,
        succ: Vec<Vec<u32>>,
    }

    /// Or, Mor, Top: player 1. And: player 2. Top and the empty tuple: Buchi self-loop. Bot and the
    /// empty union: player 1 dead end (player 1 loses there).
    fn game_of(g: &G) -> Game {
        let n = g.n();
        let mut gm = Game {
            p2: vec![false; n],
            buchi: vec![false; n],
            succ: g.c.clone(),
        };
        for v in 0..n {
            match g.k[v] {
                K::And if g.c[v].is_empty() => {
                    gm.buchi[v] = true;
                    gm.succ[v] = vec![v as u32];
                }
                K::And => gm.p2[v] = true,
                K::Top => {
                    gm.buchi[v] = true;
                    gm.succ[v] = vec![v as u32];
                }
                K::Mor => gm.buchi[v] = true,
                K::Or | K::Bot => {}
            }
        }
        gm
    }

    /// Attractor of `target` for player 2 (`p2 = true`) or player 1 inside the subgame `inv`.
    fn attractor(
        gm: &Game,
        pred: &[Vec<u32>],
        inv: &[bool],
        target: &[u32],
        p2: bool,
        work: &mut u64,
    ) -> Vec<bool> {
        let n = gm.p2.len();
        let mut a = vec![false; n];
        let mut cnt = vec![0u32; n];
        for v in 0..n {
            if inv[v] {
                cnt[v] = gm.succ[v].iter().filter(|&&w| inv[w as usize]).count() as u32;
                *work += gm.succ[v].len() as u64;
            }
        }
        let mut q = vec![];
        for &t in target {
            if inv[t as usize] && !a[t as usize] {
                a[t as usize] = true;
                q.push(t);
            }
        }
        while let Some(v) = q.pop() {
            for &u in &pred[v as usize] {
                let u = u as usize;
                *work += 1;
                if !inv[u] || a[u] {
                    continue;
                }
                if gm.p2[u] == p2 {
                    a[u] = true;
                    q.push(u as u32);
                } else {
                    cnt[u] -= 1;
                    if cnt[u] == 0 {
                        a[u] = true;
                        q.push(u as u32);
                    }
                }
            }
        }
        a
    }

    /// Winning region of player 1 (McNaughton/Zielonka iteration, O(n m)).
    fn classical(gm: &Game, work: &mut u64) -> Vec<bool> {
        let n = gm.p2.len();
        let mut pred = vec![vec![]; n];
        for v in 0..n {
            for &w in &gm.succ[v] {
                pred[w as usize].push(v as u32);
            }
        }
        let mut inv = vec![true; n];
        let dead: Vec<u32> = (0..n as u32)
            .filter(|&v| gm.succ[v as usize].is_empty())
            .collect();
        let a = attractor(gm, &pred, &inv, &dead, true, work);
        for v in 0..n {
            if a[v] {
                inv[v] = false;
            }
        }
        loop {
            let b: Vec<u32> = (0..n as u32)
                .filter(|&v| inv[v as usize] && gm.buchi[v as usize])
                .collect();
            let r = attractor(gm, &pred, &inv, &b, false, work);
            let tr: Vec<u32> = (0..n as u32)
                .filter(|&v| inv[v as usize] && !r[v as usize])
                .collect();
            if tr.is_empty() {
                return inv;
            }
            let w = attractor(gm, &pred, &inv, &tr, true, work);
            for v in 0..n {
                if w[v] {
                    inv[v] = false;
                }
            }
        }
    }

    /// Whether each node is inhabited.
    pub fn answers(g: &G) -> Vec<bool> {
        classical(&game_of(g), &mut 0)
    }
}
