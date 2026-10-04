//! Exact-integer law recursion of the lower model M1 (Section 13 of the paper, with p_L replaced
//! by its limit 1/3), rounded down to the denominator D = 2^W.
//!
//! Library of the recursion, used by the binary m1run (src/bin/m1run.rs).
//!
//! Values are naturals n standing for n / D. Types of a child: 0..3 = U_f
//! (entered, f never-entered children), 4 = N (never entered).
//! State at height h: rho_h(b, f') (lanes b*4 + f') and K_h[f](a, f')
//! (lanes a*4 + f'). Two starts: base_state, height -1 (the frogless vertex, Bernoulli(1/3)),
//! which m1run does not use; base_state_h0, height 0 (Rhat_0 and Khat_0 of Section 13 with q_L
//! replaced by 1/3), used by m1run.
//!
//! Rounding (the same in the Lean step): every new entry is
//!   ((num >> W) * c) >> W,
//! where num is an exact natural in units D^2 and c = floor(2^(2W) / div) with
//! div the exact divisor in units D; this is at most num / div.

use rayon::prelude::*;

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Mode {
    Sat,
    Drop,
    D0,
}

#[derive(Clone, Copy)]
pub struct Par {
    pub v: usize,
    pub p: usize,
    pub w: u32,
    pub mode: Mode,
}

impl Par {
    pub fn d(&self) -> u128 {
        1u128 << self.w
    }
    pub fn nl(&self) -> usize {
        (self.v + 1) * 4
    }
    pub fn sat(&self) -> bool {
        self.mode != Mode::Drop
    }
}

pub type Lanes = Vec<u128>;

#[derive(Clone)]
pub struct State {
    pub rho: Lanes,
    pub k: [Lanes; 4],
}

pub struct Diag {
    pub def_rho: u128,
    pub def_k: [u128; 4],
    pub def_b: [u128; 4],
    pub blaw: [Vec<u128>; 4], // law of the count B(k) with k entrants, k = 1..4, deficit moved to 0
}

pub fn sum(v: &[u128]) -> u128 {
    v.iter().sum()
}

/// Height -1: the frogless vertex answers each entry with Bernoulli(1/3).
pub fn base_state(par: &Par) -> State {
    let d = par.d();
    let t = d / 3;
    let mut rho = vec![0u128; par.nl()];
    rho[4] = t; // b = 1, f' = 0
    rho[0] = d - t;
    let mut k: [Lanes; 4] = Default::default();
    for f in 0..4 {
        let mut l = vec![0u128; par.nl()];
        l[4 + f] = t; // a = 1, f' = f
        l[f] = d - t; // a = 0, f' = f
        k[f] = l;
    }
    State { rho, k }
}

/// Height 0, Rhat_0 and Khat_0 of Section 13 of the paper with q_L replaced by its limit 1/3:
/// Rhat_0 is the law of min(Bin(2, 1/3), V) in b with f = 0, Khat_0(f -> .) puts 2/3 at (0, f)
/// and 1/3 at (1, f).
/// Each entry is rounded down to the grid 2^-W and the deficit is moved to the bottom (0, 0).
pub fn base_state_h0(par: &Par) -> State {
    let d = par.d();
    let nl = par.nl();
    let v = par.v;
    // Bin(2, 1/3): 4/9, 4/9, 1/9 at b = 0, 1, 2 (b clipped at V)
    let mut rho = vec![0u128; nl];
    rho[4 * 1.min(v)] += 4 * d / 9;
    rho[4 * 2.min(v)] += d / 9;
    rho[0] += d - sum(&rho);
    let mut k: [Lanes; 4] = Default::default();
    for f in 0..4 {
        let mut l = vec![0u128; nl];
        l[4 + f] = d / 3;
        l[f] += 2 * d / 3;
        l[0] += d - sum(&l);
        k[f] = l;
    }
    State { rho, k }
}

/// H_1 kernel at height h from rhobar_{h-1}: the rows Y_f(1), rounded down, before the
/// deficit is moved to the bottom.
pub fn kernel_raw(par: &Par, rb: &[u128]) -> [Lanes; 4] {
    let (v, p, w) = (par.v, par.p, par.w);
    let d = par.d();
    let nl = par.nl();
    let mut y: Vec<Vec<Lanes>> = Vec::with_capacity(4);
    for f in 0..4usize {
        let c = d / (9 + f as u128); // floor(2^(2W) / ((9 + f) D))
        let mut rows: Vec<Lanes> = Vec::with_capacity(p + 1);
        let mut r0 = vec![0u128; nl];
        r0[f] = d;
        rows.push(r0);
        let ghost = par.mode == Mode::D0;
        for s in 1..=p {
            let prev = &rows[s - 1];
            let mut row = vec![0u128; nl];
            for a in 0..=v {
                for g in 0..4 {
                    let mut up = if a >= 1 { prev[(a - 1) * 4 + g] } else { 0 };
                    if a == v && par.sat() {
                        up += prev[v * 4 + g];
                    }
                    let same = prev[a * 4 + g];
                    let num = if ghost {
                        3 * d * up + 6 * d * same
                    } else {
                        let mut num = 3 * d * up + 2 * (3 - f as u128) * d * same;
                        if f >= 1 {
                            let yf = &y[f - 1];
                            let mut acc = 0u128;
                            for b in 0..=v {
                                let ss = (s - 1 + b).min(p);
                                acc += rb[b] * yf[ss][a * 4 + g];
                            }
                            num += 3 * f as u128 * acc;
                        }
                        num
                    };
                    let cc = if ghost { d / 9 } else { c };
                    row[a * 4 + g] = ((num >> w) * cc) >> w;
                }
            }
            rows.push(row);
        }
        y.push(rows);
    }
    let mut out: [Lanes; 4] = Default::default();
    for f in 0..4 {
        out[f] = y[f][1].clone();
    }
    out
}

/// H_1 kernel at height h from rhobar_{h-1} (backward DP over the pool).
pub fn kernel(par: &Par, rb: &[u128]) -> ([Lanes; 4], [u128; 4]) {
    let d = par.d();
    let v = par.v;
    let y1 = kernel_raw(par, rb);
    let mut k: [Lanes; 4] = Default::default();
    let mut def = [0u128; 4];
    for f in 0..4 {
        let mut l = y1[f].clone();
        let s = sum(&l);
        assert!(s <= d);
        def[f] = d - s;
        l[0] += d - s;
        // structural checks: f' <= f, and f' = f only with a <= 1
        for a in 0..=v {
            for g in 0..4 {
                let x = l[a * 4 + g];
                if g > f || (g == f && a >= 2) {
                    assert_eq!(x, 0, "kernel lane a={a} f'={g} f={f}");
                }
            }
        }
        k[f] = l;
    }
    (k, def)
}

pub fn sig_idx(t: [usize; 3]) -> usize {
    let mut s = t;
    s.sort_unstable_by(|a, b| b.cmp(a));
    s[0] * 25 + s[1] * 5 + s[2]
}

fn sigmas() -> Vec<[usize; 3]> {
    let mut out = Vec::new();
    for a in 0..5 {
        for b in 0..=a {
            for c in 0..=b {
                out.push([a, b, c]);
            }
        }
    }
    // events lower the sum of the types
    out.sort_by_key(|s| (s[0] + s[1] + s[2], s[0] * 25 + s[1] * 5 + s[2]));
    out
}

struct Channel {
    target: usize,
    col: Vec<u128>, // answer law times multiplicity, entries 0..=V
}

/// R closure at height h from (rho_{h-1}, K_{h-1}): all tables W_sigma.
pub fn closure(par: &Par, st: &State) -> Vec<Option<Vec<Lanes>>> {
    let (v, p, w) = (par.v, par.p, par.w);
    let d = par.d();
    let nl = par.nl();
    let mut tab: Vec<Option<Vec<Lanes>>> = vec![None; 125];
    for sg in sigmas() {
        let n_n = sg.iter().filter(|&&t| t == 4).count();
        // loop and loss weights, channels
        let mut lp = 0u128;
        let mut lo = 0u128;
        let mut chans: Vec<Channel> = Vec::new();
        let mut seen = [false; 5];
        for i in 0..3 {
            let t = sg[i];
            if t < 4 {
                lp += st.k[t][4 + t];
                lo += st.k[t][t];
            }
            if seen[t] {
                continue;
            }
            seen[t] = true;
            let mult = sg.iter().filter(|&&u| u == t).count() as u128;
            let (law, maxf): (&Lanes, usize) = if t == 4 { (&st.rho, 4) } else { (&st.k[t], t) };
            for f2 in 0..maxf {
                let mut ns = sg;
                ns[i] = f2;
                let col: Vec<u128> = (0..=v).map(|a| mult * law[a * 4 + f2]).collect();
                if col.iter().all(|&x| x == 0) {
                    continue;
                }
                chans.push(Channel { target: sig_idx(ns), col });
            }
        }
        let div = 4 * d - lp;
        let c = (1u128 << (2 * w)) / div;
        // event term E(p), p = 1..=P, in parallel over p
        let e: Vec<Lanes> = (1..=p)
            .into_par_iter()
            .map(|pp| {
                let mut acc = vec![0u128; nl];
                for ch in &chans {
                    let wt = tab[ch.target].as_ref().unwrap();
                    for (ans, &q) in ch.col.iter().enumerate() {
                        if q == 0 {
                            continue;
                        }
                        let row = &wt[(pp - 1 + ans).min(p)];
                        for (o, &x) in acc.iter_mut().zip(row.iter()) {
                            *o += q * x;
                        }
                    }
                }
                acc
            })
            .collect();
        let mut rows: Vec<Lanes> = Vec::with_capacity(p + 1);
        let mut r0 = vec![0u128; nl];
        r0[n_n] = d;
        rows.push(r0);
        for pp in 1..=p {
            let prev = &rows[pp - 1];
            let ep = &e[pp - 1];
            let mut row = vec![0u128; nl];
            for x in 0..=v {
                for g in 0..4 {
                    let mut up = if x >= 1 { prev[(x - 1) * 4 + g] } else { 0 };
                    if x == v && par.sat() {
                        up += prev[v * 4 + g];
                    }
                    let num = d * up + lo * prev[x * 4 + g] + ep[x * 4 + g];
                    row[x * 4 + g] = ((num >> w) * c) >> w;
                }
            }
            assert!(sum(&row) <= d);
            rows.push(row);
        }
        tab[sig_idx(sg)] = Some(rows);
    }
    tab
}

pub fn step(par: &Par, st: &State) -> (State, Diag) {
    let d = par.d();
    let v = par.v;
    let rb: Vec<u128> = (0..=v).map(|b| (0..4).map(|g| st.rho[b * 4 + g]).sum()).collect();
    let (k, def_k) = kernel(par, &rb);
    let tab = closure(par, st);
    let nnn = tab[124].as_ref().unwrap();
    let mut rho = nnn[2].clone();
    let s = sum(&rho);
    let def_rho = d - s;
    rho[0] += def_rho;
    let mut blaw: [Vec<u128>; 4] = Default::default();
    let mut def_b = [0u128; 4];
    for kk in 1..=4 {
        let row = &nnn[kk + 1];
        let mut l: Vec<u128> = (0..=v).map(|x| (0..4).map(|g| row[x * 4 + g]).sum()).collect();
        let s = sum(&l);
        def_b[kk - 1] = d - s;
        l[0] += d - s;
        blaw[kk - 1] = l;
    }
    (State { rho, k }, Diag { def_rho, def_k, def_b, blaw })
}


/// One height from the stored state of height h - 1, rounded down, nothing moved to the
/// bottom: (rho~_h, K~_h(f -> .) for f = 0..3, the rows W_NNN(p), p = 0..P, of the R closure
/// at height h; W_NNN(q) is Wtop_q of the vertex at height h).
pub fn step_raw(par: &Par, st: &State) -> (Lanes, [Lanes; 4], Vec<Lanes>) {
    let v = par.v;
    let rb: Vec<u128> = (0..=v).map(|b| (0..4).map(|g| st.rho[b * 4 + g]).sum()).collect();
    let k = kernel_raw(par, &rb);
    let mut tab = closure(par, st);
    let nnn = tab[124].take().unwrap();
    (nnn[2].clone(), k, nnn)
}
