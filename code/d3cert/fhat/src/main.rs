// d3-fhat: iteration of the bounds of Lemma 11.2 of the paper (end configurations), d = 3, the planted
// model itself.
//
// For a height m two families of upper bounds are carried:
//   F[k][g] >= P(G_m(k) <= g)          (cdf upper bounds, k = 0..E, g = 0..GM),
//   D[k]    >= mu_m(k) - E G_m(k)      (deficits, mu_m(k) = (m + 1 + k)/3).
// Height -1 is the empty subtree: G(k) ~ Bin(k, 1/3) exactly, deficit 0.
// A vertex at height m + 1 with q = j + 1 initial frogs has three children at height m.
// End-configuration bound: {N = n} is contained in {T(n) = n}, T(n) = q + sum_c G_c(k_c(n)),
// k(n) the direction counts of D_1..D_n, independent of the children's curves. Hence
//   (A) P(G_{m+1}(j) <= v) <= sum over e in [0,E)^3 and s of W_e(s) P(sum_c G_c(e_c) = s)
//         + 3 P(Bin(E + v, 1/2) >= E) P(G_m(E) <= n0 - q - 1) + P(Bin(n0, 1/4) <= v),
//       W_e(s) = Mult(q + s; q + s - M, e) 1{0 <= q + s - M <= v, q + s < n0}, M = |e|;
//   (B) P(e_1 < J) <= the same sum over e_1 < J, e_2, e_3 < E, with W_e(s) = Mult 1{q + s >= M,
//       q + s < K}, + 2 P(Bin(E + J - 1, 1/2) >= E) P(G_m(E) <= K - q - 1) + P(Bin(K, 1/4) < J).
// Remainders: a child c with e_c >= E has G_c(E) <= N - q, and its E-th entry comes before the
// (v+1)-th up step (A) or before the J-th entry into child 1 (B); the direction event and the
// curve event are independent, and up and c (or child 1 and c) are equally likely directions.
// The children's laws enter through cdf upper bounds only: W_e is replaced by its nonincreasing
// envelope in s, and each G_c(e_c) by the stochastically smallest law with cdf F[e_c]. Since
// W_e(s) = (M!/(e_1! e_2! e_3!)) C(q + s, M) 4^-(q + s) 1{...} and the indicator depends on e only
// through M, the sum is sum_M sum_s Psi_M(s) Z_M(s), Psi_M the envelope of C(q + s, M) 4^-(q + s)
// on the window, Z_M(s) = sum over |e| = M of the multinomial coefficient times the convolution
// of the three pseudo-pmfs (computed once per height).
// Deficits: Lemma 10.7 (2) (from Lemmas 10.5 and 10.6) gives D'(j) <= D(J) (1 - P_B) + mu_m(J) P_B
// for every J >= 1, P_B the bound (B) at (j, J); J = 0 gives D'(j) <= (m + 1)/3.
// cdf at height m + 1: min of (A), the coin bound P(Bin(j, 1/3) <= v) (Lemma 10.3), the deficit
// bounds (Lemma 11.1 (3)), monotonicity in j and in v.
//
// Usage: d3-fhat E GM VM JM MMAX EVERY THREADS [M0 DELTA1 DELTAINF [ML MH ETA [FLOOR]]]
//   E entries tracked (0..E), GM pseudo-law range, VM largest v in (A), JM largest J in (B).
//   The optional seed replaces height -1 by a hypothetical height M0 with
//   D(k) = mu_M0(k) (DELTA1 4^-(k-1) + DELTAINF) and F from the coin and deficit bounds only
//   (an ablation that tests whether the induction step closes; it proves nothing). DELTA1 < 0
//   seeds from E G_M0(1) >= (1 - DELTAINF) mu_M0(1) alone: D(k) <= D(1) for every k, because
//   E[G(k+1) - G(k)] >= 1/3 = mu(k+1) - mu(k) (Lemma 10.3).
// Supersolution search (ML MH ETA [FLOOR]): iterate to ML, inflate the state by 1 + ETA (cdf bounds
// and normalized deficits; FLOOR is added to the cdf bounds), then Kleene iterations
// T <- max(T, (1 + FHAT_KETA) Phi_worst(T) + FLOOR) (FHAT_NIT of them, default 1 = plain check),
// Phi_worst = one worst-case step for children heights ML..MH-1 (deficit ratios mu_m(J)/mu_(m+1)(j) at
// their worst end, deficit cdf bounds at the lowest height). A T with Phi_worst(T) <= T is valid at
// every height of [ML, MH] (Lemma 12.5 (4)). FHAT_PBTAB prints P_B(j, J).
// FHAT_LOAD=path starts from a saved state (FHAT_SAVE=path writes one), extended to larger E and GM
// by monotonicity in k, Lemma 10.7 (1), and the coin and deficit bounds; FHAT_SAVEAT=h1,h2,... with
// FHAT_SAVEDIR=dir also writes the states at those heights. In the search, FHAT_BELL=beta solves the
// deficit part as a Bellman system, FHAT_MARGIN=phi_f,phi_d requires absorbing margins, and
// FHAT_KAPPA=kappa a strict relative margin (1 + kappa) Phi_worst(T) <= T. FHAT_FMEAN adds deficits
// read off the cdf bounds, FHAT_CDF prints cdf bounds and the raw bound (A), FHAT_OPS prints
// operation counts per step. FHAT_SPINE adds the spine bounds S2 (deficits) and S3 (cdf rows) of
// Lemma 12.1 to every step and check (the step map Phi of Definition 12.3); FHAT_SPINE=s2 or
// FHAT_SPINE=s3 keeps one of them (an ablation), FHAT_SPINE_CHECK compares their laws with a forward
// computation, and FHAT_OPS also counts their multiply-adds.
// FHAT_HROWS adds hand-over tests against other rows of Theorem 14.1 after a PASS (see there),
// FHAT_SAVET=path writes the T of a PASS for the outward-rounded check of ../cert (d3-cert tcheck).
// Floating point (f64) without directed rounding, so the output is numerical evidence.

use std::env;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

// operation counters (FHAT_OPS): multiply-adds in the convolutions, terms and exponentials in the queries
static CONV_OPS: AtomicU64 = AtomicU64::new(0);
static QUERY_OPS: AtomicU64 = AtomicU64::new(0);
static EXP_OPS: AtomicU64 = AtomicU64::new(0);
// multiply-adds in the spine laws (stage_laws), printed on a separate line when FHAT_SPINE is set
static SPINE_OPS: AtomicU64 = AtomicU64::new(0);
// multiply-adds in the S4 laws (s4_laws), printed with the spine line when FHAT_S4 is set
static S4_OPS: AtomicU64 = AtomicU64::new(0);

fn lnfact_table(n: usize) -> Vec<f64> {
    let mut t = vec![0.0f64; n + 1];
    for i in 1..=n {
        t[i] = t[i - 1] + (i as f64).ln();
    }
    t
}

// P(Bin(n, p) <= v), summed in log space
fn binom_le(lf: &[f64], n: usize, p: f64, v: i64) -> f64 {
    if v < 0 {
        return 0.0;
    }
    if v as usize >= n {
        return 1.0;
    }
    let (lp, lq) = (p.ln(), (1.0 - p).ln());
    let mut s = 0.0;
    for k in 0..=(v as usize) {
        s += (lf[n] - lf[k] - lf[n - k] + k as f64 * lp + (n - k) as f64 * lq).exp();
    }
    s.min(1.0)
}

fn mu(m: i64, k: usize) -> f64 {
    (m as f64 + 1.0 + k as f64) / 3.0
}

// cdf upper bound from a deficit: Lemma 11.1 (3) of the paper, second and third bounds
fn defbound(dl: f64, mu: f64, g: usize) -> f64 {
    let g = g as f64;
    let mut b: f64 = 1.0;
    if mu > g + 1.0 {
        b = b.min((dl + mu.sqrt() / 2.0) / (mu - g - 1.0));
    }
    for i in 1..200 {
        let t = i as f64 / 200.0;
        let den = (1.0 - t) * mu - g;
        if den > 0.0 {
            b = b.min(dl / den + (-t * t * mu / 2.0).exp());
        }
    }
    b.max(0.0)
}

// truncated convolution of a and b, length len
fn conv(a: &[f64], b: &[f64], len: usize) -> Vec<f64> {
    let mut h = vec![0.0f64; len];
    let mut ops = 0u64;
    for (i, &x) in a.iter().enumerate().take(len) {
        if x == 0.0 {
            continue;
        }
        ops += (len - i) as u64;
        for (k, &y) in b[..len - i].iter().enumerate() {
            h[i + k] += x * y;
        }
    }
    CONV_OPS.fetch_add(ops, Relaxed);
    h
}

// Value of a policy for the deficit Bellman system val(j) = min(c0(j), min_J a(j, J) val(J) + b(j, J)):
// pol[j] = 0 (the constant c0(j)) or J in 1..JM. The policy graph is functional; a cycle with
// product of a's below 1 is solved exactly, one with product >= 1 gets +infinity (improper).
fn eval_policy(pol: &[usize], a: &[Vec<f64>], b: &[Vec<f64>], c0: &[f64], lo: &[f64]) -> Vec<f64> {
    let n = pol.len();
    let mut val = vec![f64::INFINITY; n];
    let mut state = vec![0u8; n];
    for start in 1..n {
        if state[start] == 2 {
            continue;
        }
        let mut path: Vec<usize> = Vec::new();
        let mut x = start;
        loop {
            if state[x] == 2 {
                break;
            }
            if state[x] == 1 {
                let pos = path.iter().position(|&y| y == x).unwrap();
                let cyc: Vec<usize> = path[pos..].to_vec();
                let k = cyc.len();
                // val(cyc[i]) = max(cc, aa x + bb) with x = val(cyc[0]); the least fixed point is
                // max(cc, bb / (1 - aa)) when aa < 1
                let (mut cc, mut aa, mut bb) = (f64::NEG_INFINITY, 1.0f64, 0.0f64);
                for &y in cyc.iter().rev() {
                    let jj = pol[y];
                    cc = lo[y].max(a[y][jj] * cc + b[y][jj]);
                    bb = a[y][jj] * bb + b[y][jj];
                    aa *= a[y][jj];
                }
                val[cyc[0]] = if aa < 1.0 {
                    cc.max(bb / (1.0 - aa))
                } else {
                    f64::INFINITY
                };
                state[cyc[0]] = 2;
                for idx in (1..k).rev() {
                    let y = cyc[idx];
                    let jj = pol[y];
                    val[y] = lo[y].max(a[y][jj] * val[cyc[(idx + 1) % k]] + b[y][jj]);
                    state[y] = 2;
                }
                path.truncate(pos);
                break;
            }
            if pol[x] == 0 {
                val[x] = lo[x].max(c0[x]);
                state[x] = 2;
                break;
            }
            state[x] = 1;
            path.push(x);
            x = pol[x];
        }
        for &y in path.iter().rev() {
            let jj = pol[y];
            val[y] = lo[y].max(a[y][jj] * val[jj] + b[y][jj]);
            state[y] = 2;
        }
    }
    val
}

// Least solution above lo of val = max(lo, Bellman(val)), by policy iteration from the all-constant
// policy (lo = 0: the least fixed point of the Bellman operator).
fn bellman(
    a: &[Vec<f64>],
    b: &[Vec<f64>],
    c0: &[f64],
    lo: &[f64],
    jm: usize,
) -> (Vec<f64>, Vec<usize>, usize) {
    let n = c0.len();
    let mut pol = vec![0usize; n];
    let mut val = eval_policy(&pol, a, b, c0, lo);
    let mut it = 0;
    loop {
        it += 1;
        let mut changed = false;
        let mut np = pol.clone();
        for j in 1..n {
            let cur = if pol[j] == 0 {
                c0[j]
            } else {
                a[j][pol[j]] * val[pol[j]] + b[j][pol[j]]
            };
            let mut best = cur;
            let mut bj = pol[j];
            if c0[j] < best * (1.0 - 1e-12) {
                best = c0[j];
                bj = 0;
            }
            for jj in 1..=jm {
                let v = a[j][jj] * val[jj] + b[j][jj];
                if v < best * (1.0 - 1e-12) {
                    best = v;
                    bj = jj;
                }
            }
            if bj != pol[j] {
                np[j] = bj;
                changed = true;
            }
        }
        if !changed || it > 500 {
            return (val, pol, it);
        }
        let nv = eval_policy(&np, a, b, c0, lo);
        // keep the old choice where the new policy is improper
        for j in 1..n {
            if !nv[j].is_finite() {
                np[j] = pol[j];
            }
        }
        pol = np;
        val = eval_policy(&pol, a, b, c0, lo);
    }
}

fn save_state(lev: &Lev, ee: usize, gm: usize, path: &str) {
    let mut s = format!("{} {} {}\n", lev.m, ee, gm);
    for k in 0..=ee {
        s.push_str(&format!("{:e}", lev.d[k]));
        for g in 0..=gm {
            s.push_str(&format!(" {:e}", lev.f[k][g]));
        }
        s.push('\n');
    }
    std::fs::write(path, s).unwrap();
}

// Spine laws (a^(2) and a^(3) of Lemma 12.1 of the paper): the lower closure at w with q initial
// frogs whose live children answer R (pseudo-law r of F(1, .), r[0..=GM+1], the residual mass at
// GM + 1) at their first entry and a Bernoulli(1/3) coin at each later entry. Staged jump chain,
// f = number of live children entered:
// a step counts with probability pc[f], enters a new live child with pn[f] (the pool gains R, f + 1),
// or is gone; the last stage has pn = 0. First-step analysis from the last stage backwards:
// A_f(y) = pc shift(A_f(y - 1)) + pg A_f(y - 1) + pn sum_r r[r] A_{f+1}(y - 1 + r), A_f(0) = delta_0,
// the count capped at cap. The pool at stage f is at most q + f (GM + 1), so no cap on the pool.
// Returns A_0(y) for y = 0..=y0.
fn stage_laws(r: &[f64], pc: &[f64], pn: &[f64], cap: usize, y0: usize) -> Vec<Vec<f64>> {
    let ns = pc.len();
    let rmax = r.len() - 1;
    let shift_add = |dst: &mut [f64], src: &[f64], w: f64| {
        for (k, &x) in src.iter().enumerate() {
            dst[(k + 1).min(cap)] += w * x;
        }
    };
    let ylim = |f: usize| y0 + f * rmax;
    // last stage: count ~ Bin(y, pc), capped
    let fl = ns - 1;
    let mut nxt: Vec<Vec<f64>> = Vec::with_capacity(ylim(fl) + 1);
    let mut a0 = vec![0.0f64; cap + 1];
    a0[0] = 1.0;
    nxt.push(a0);
    for y in 1..=ylim(fl) {
        let mut a = vec![0.0f64; cap + 1];
        let prev = &nxt[y - 1];
        for k in 0..=cap {
            a[k] += (1.0 - pc[fl]) * prev[k];
        }
        shift_add(&mut a, prev, pc[fl]);
        nxt.push(a);
    }
    for f in (0..fl).rev() {
        let pg = 1.0 - pc[f] - pn[f];
        let mut cur: Vec<Vec<f64>> = Vec::with_capacity(ylim(f) + 1);
        let mut a0 = vec![0.0f64; cap + 1];
        a0[0] = 1.0;
        cur.push(a0);
        for y in 1..=ylim(f) {
            let mut a = vec![0.0f64; cap + 1];
            let prev = &cur[y - 1];
            for k in 0..=cap {
                a[k] += pg * prev[k];
            }
            shift_add(&mut a, prev, pc[f]);
            for (rv, &rp) in r.iter().enumerate() {
                if rp == 0.0 {
                    continue;
                }
                let w = pn[f] * rp;
                for (k, &x) in nxt[y - 1 + rv].iter().enumerate() {
                    a[k] += w * x;
                }
                SPINE_OPS.fetch_add(cap as u64 + 1, Relaxed);
            }
            cur.push(a);
        }
        nxt = cur;
    }
    nxt
}

// S2 (dead child c, live s_1, s_2): law of min(e''_c, E); S3 (three live children): law of
// min(X'', GM + 1); both for q = 1..=E + 1 (index q).
fn spine_laws(f1: &[f64], ee: usize, gm: usize) -> (Vec<Vec<f64>>, Vec<Vec<f64>>) {
    let mut r = vec![0.0f64; gm + 2];
    let mut prev = 0.0f64;
    for g in 0..=gm {
        r[g] = (f1[g] - prev).max(0.0);
        prev = prev.max(f1[g]);
    }
    r[gm + 1] = (1.0 - prev).max(0.0);
    let s2 = stage_laws(&r, &[0.25, 3.0 / 11.0, 0.3], &[0.5, 3.0 / 11.0, 0.0], ee, ee + 1);
    let s3 = stage_laws(
        &r,
        &[0.25, 3.0 / 11.0, 0.3, 1.0 / 3.0],
        &[0.75, 6.0 / 11.0, 0.3, 0.0],
        gm + 1,
        ee + 1,
    );
    (s2, s3)
}

// Independent check of stage_laws (FHAT_SPINE_CHECK), in forward form: the pool distribution is pushed
// frog by frog from the largest pool down, the new pools after a new child are convolved with r, stage
// by stage.
fn stage_forward(r: &[f64], pc: &[f64], pn: &[f64], cap: usize, q: usize) -> Vec<f64> {
    let ns = pc.len();
    let rmax = r.len() - 1;
    let yc = q + ns * rmax;
    let mut out = vec![0.0f64; cap + 1];
    let mut dist = vec![vec![0.0f64; cap + 1]; yc + 1];
    dist[q][0] = 1.0;
    for f in 0..ns {
        if f == ns - 1 {
            for y in 0..=yc {
                // count += Bin(y, pc): push frog by frog
                let mut cur = dist[y].clone();
                for _ in 0..y {
                    let mut nx = vec![0.0f64; cap + 1];
                    for k in 0..=cap {
                        nx[k] += (1.0 - pc[f]) * cur[k];
                        nx[(k + 1).min(cap)] += pc[f] * cur[k];
                    }
                    cur = nx;
                }
                for k in 0..=cap {
                    out[k] += cur[k];
                }
            }
            break;
        }
        let pg = 1.0 - pc[f] - pn[f];
        let mut ex = vec![vec![0.0f64; cap + 1]; yc + 1];
        for y in (1..=yc).rev() {
            for k in 0..=cap {
                let x = dist[y][k];
                if x == 0.0 {
                    continue;
                }
                dist[y][k] = 0.0;
                ex[y - 1][k] += x * pn[f];
                dist[y - 1][(k + 1).min(cap)] += x * pc[f];
                dist[y - 1][k] += x * pg;
            }
        }
        for k in 0..=cap {
            out[k] += dist[0][k];
            dist[0][k] = 0.0;
        }
        for y in 0..=yc {
            for k in 0..=cap {
                let x = ex[y][k];
                if x == 0.0 {
                    continue;
                }
                for (rv, &rp) in r.iter().enumerate() {
                    if rp != 0.0 && y + rv <= yc {
                        dist[y + rv][k] += x * rp;
                    }
                }
            }
        }
    }
    out
}

// S4 release term (not in the paper): a lower process of the closure with the release rule "largest
// held batch first", children answering a released batch b with the pseudo-law of F^(min(b, EB), .),
// F^ the rows of F made nonincreasing in k. Between releases the frogs at w have i.i.d. fates; with r
// children released, a frog ends up (self-loops of the coin returns removed) with probability 3/(12 - r)
// at each of up and the unreleased children (a dead child counts as unreleased), 2r/(12 - r) lost.
// Backward over the releases: H2 (one unreleased child left) and H1 (two left) are the laws of the
// count increment from a pool of y frogs given the unreleased batches; W(B, s..) mixes them over the
// answer to the released batch B. Returns, for q = 2..=JMAX + 1 (index q): the law of min(X*, GM + 1)
// (three live children, X* the ups) and the law of min(e*_c, E) (c dead, two live siblings, e*_c the
// entries into c).
fn s4_laws(
    f: &[Vec<f64>],
    ee: usize,
    gm: usize,
    eb: usize,
    jmax: usize,
    lf: &[f64],
) -> (Vec<Vec<f64>>, Vec<Vec<f64>>) {
    let cap = gm + 1; // ups capped at GM + 1
    let l = cap + 1;
    let ymax = gm + 1; // answers are at most GM + 1
    let mut py = vec![vec![0.0f64; ymax + 1]; eb + 1];
    let mut fr = vec![1.0f64; gm + 1];
    for b in 1..=eb {
        for g in 0..=gm {
            fr[g] = fr[g].min(f[b][g]);
        }
        let mut prev = 0.0f64;
        for g in 0..=gm {
            py[b][g] = (fr[g] - prev).max(0.0);
            prev = prev.max(fr[g]);
        }
        py[b][gm + 1] = (1.0 - prev).max(0.0);
    }
    let binrows = |p: f64, c: usize| -> Vec<Vec<f64>> {
        let mut rows = Vec::with_capacity(ymax + 1);
        let mut r = vec![0.0f64; c + 1];
        r[0] = 1.0;
        rows.push(r.clone());
        for _ in 1..=ymax {
            let mut nx = vec![0.0f64; c + 1];
            for k in 0..=c {
                nx[k] += (1.0 - p) * r[k];
                nx[(k + 1).min(c)] += p * r[k];
            }
            r = nx;
            rows.push(r.clone());
        }
        rows
    };
    let unit = |len: usize| -> Vec<f64> {
        let mut v = vec![0.0f64; len];
        v[0] = 1.0;
        v
    };
    // mix over the answer to batch b of the rows indexed by the pool
    let mix = |b: usize, rows: &[Vec<f64>]| -> Vec<f64> {
        let mut v = vec![0.0f64; rows[0].len()];
        for (y, &w) in py[b].iter().enumerate() {
            if w == 0.0 {
                continue;
            }
            for (x, &z) in rows[y].iter().enumerate() {
                v[x] += w * z;
            }
            S4_OPS.fetch_add(rows[0].len() as u64, Relaxed);
        }
        v
    };
    let mult = |parts: &[usize]| -> f64 {
        let n: usize = parts.iter().sum();
        (lf[n] - parts.iter().map(|&k| lf[k]).sum::<f64>() - n as f64 * 4f64.ln()).exp()
    };
    let qmax = jmax + 1;

    // three live children: the ups
    let b13 = binrows(1.0 / 3.0, cap);
    let w3: Vec<Vec<f64>> = (0..=eb).map(|s| if s == 0 { unit(l) } else { mix(s, &b13) }).collect();
    let mut h2: Vec<Vec<Vec<f64>>> = vec![w3];
    for y in 1..=ymax {
        let p = &h2[y - 1];
        let cur: Vec<Vec<f64>> = (0..=eb)
            .map(|s| {
                let sp = (s + 1).min(eb);
                let mut v = vec![0.0f64; l];
                for x in 0..l {
                    v[(x + 1).min(cap)] += 0.3 * p[s][x];
                    v[x] += 0.3 * p[sp][x] + 0.4 * p[s][x];
                }
                v
            })
            .collect();
        S4_OPS.fetch_add(((eb + 1) * l * 3) as u64, Relaxed);
        h2.push(cur);
    }
    // W2[B][s], B >= 1 the released batch, s <= B the other one
    let mut w2: Vec<Vec<Vec<f64>>> = vec![Vec::new(); eb + 1];
    for bb in 1..=eb {
        w2[bb] = (0..=bb)
            .map(|s| {
                let rows: Vec<Vec<f64>> = (0..=ymax).map(|y| h2[y][s].clone()).collect();
                mix(bb, &rows)
            })
            .collect();
    }
    drop(h2);
    // sorted pairs s1 >= s2 of unreleased batches, and the triples (B >= s1 >= s2) that phase 0 reaches
    let pid = |s1: usize, s2: usize| -> usize {
        let (a, b) = if s1 >= s2 { (s1, s2) } else { (s2, s1) };
        a * (a + 1) / 2 + b
    };
    let npair = (eb + 1) * (eb + 2) / 2;
    let mut need = vec![vec![false; npair]; eb + 1];
    for q in 2..=qmax {
        for u0 in 0..=q {
            for b1 in 0..=(q - u0) {
                for b2 in 0..=(q - u0 - b1) {
                    let b3 = q - u0 - b1 - b2;
                    let mut t = [b1.min(eb), b2.min(eb), b3.min(eb)];
                    t.sort_unstable_by(|a, b| b.cmp(a));
                    if t[0] > 0 {
                        need[t[0]][pid(t[1], t[2])] = true;
                    }
                }
            }
        }
    }
    let mut w1: Vec<Vec<Vec<f64>>> = (0..=eb)
        .map(|bb| (0..npair).map(|p| if need[bb][p] { vec![0.0f64; l] } else { Vec::new() }).collect())
        .collect();
    let mut pairs = Vec::with_capacity(npair);
    for s1 in 0..=eb {
        for s2 in 0..=s1 {
            pairs.push((s1, s2));
        }
    }
    let mut h1: Vec<Vec<f64>> = pairs
        .iter()
        .map(|&(s1, s2)| if s1 == 0 { unit(l) } else { w2[s1][s2].clone() })
        .collect();
    for y in 0..=ymax {
        if y > 0 {
            let p = &h1;
            let cur: Vec<Vec<f64>> = pairs
                .iter()
                .map(|&(s1, s2)| {
                    let (i0, i1, i2) = (pid(s1, s2), pid((s1 + 1).min(eb), s2), pid(s1, (s2 + 1).min(eb)));
                    let mut v = vec![0.0f64; l];
                    for x in 0..l {
                        v[(x + 1).min(cap)] += (3.0 / 11.0) * p[i0][x];
                        v[x] += (3.0 / 11.0) * (p[i1][x] + p[i2][x]) + (2.0 / 11.0) * p[i0][x];
                    }
                    v
                })
                .collect();
            S4_OPS.fetch_add((npair * l * 4) as u64, Relaxed);
            h1 = cur;
        }
        for bb in 1..=eb {
            let w = py[bb][y];
            if w == 0.0 {
                continue;
            }
            for p in 0..npair {
                if need[bb][p] {
                    for x in 0..l {
                        w1[bb][p][x] += w * h1[p][x];
                    }
                    S4_OPS.fetch_add(l as u64, Relaxed);
                }
            }
        }
    }
    let mut lawx = vec![Vec::new(); qmax + 1];
    for q in 2..=qmax {
        let mut v = vec![0.0f64; l];
        for u0 in 0..=q {
            for b1 in 0..=(q - u0) {
                for b2 in 0..=(q - u0 - b1) {
                    let b3 = q - u0 - b1 - b2;
                    let w = mult(&[u0, b1, b2, b3]);
                    let mut t = [b1.min(eb), b2.min(eb), b3.min(eb)];
                    t.sort_unstable_by(|a, b| b.cmp(a));
                    if t[0] == 0 {
                        v[u0.min(cap)] += w;
                    } else {
                        for (x, &z) in w1[t[0]][pid(t[1], t[2])].iter().enumerate() {
                            v[(x + u0).min(cap)] += w * z;
                        }
                    }
                }
            }
        }
        lawx[q] = v;
    }

    // c dead, two live siblings: the entries into c
    let ce = ee;
    let b310 = binrows(0.3, ce);
    let w2d: Vec<Vec<f64>> = (0..=eb).map(|s| if s == 0 { unit(ce + 1) } else { mix(s, &b310) }).collect();
    let mut h1d: Vec<Vec<Vec<f64>>> = vec![w2d];
    for y in 1..=ymax {
        let p = &h1d[y - 1];
        let cur: Vec<Vec<f64>> = (0..=eb)
            .map(|s| {
                let sp = (s + 1).min(eb);
                let mut v = vec![0.0f64; ce + 1];
                for x in 0..=ce {
                    v[(x + 1).min(ce)] += (3.0 / 11.0) * p[s][x];
                    v[x] += (3.0 / 11.0) * p[sp][x] + (5.0 / 11.0) * p[s][x];
                }
                v
            })
            .collect();
        h1d.push(cur);
    }
    let mut w1d: Vec<Vec<Vec<f64>>> = vec![Vec::new(); eb + 1];
    for bb in 1..=eb {
        w1d[bb] = (0..=bb)
            .map(|s| {
                let rows: Vec<Vec<f64>> = (0..=ymax).map(|y| h1d[y][s].clone()).collect();
                mix(bb, &rows)
            })
            .collect();
    }
    let mut lawe = vec![Vec::new(); qmax + 1];
    for q in 2..=qmax {
        let mut v = vec![0.0f64; ce + 1];
        for u in 0..=q {
            for kc in 0..=(q - u) {
                for b1 in 0..=(q - u - kc) {
                    let b2 = q - u - kc - b1;
                    let w = mult(&[u, kc, b1, b2]);
                    let (hi, lo) = (b1.max(b2).min(eb), b1.min(b2).min(eb));
                    if hi == 0 {
                        v[kc.min(ce)] += w;
                    } else {
                        for (x, &z) in w1d[hi][lo].iter().enumerate() {
                            v[(x + kc).min(ce)] += w * z;
                        }
                    }
                }
            }
        }
        lawe[q] = v;
    }
    (lawx, lawe)
}

// Monte Carlo of the S4 process (FHAT_S4_CHECK), an independent check of s4_laws: frogs stepped one at a
// time with explicit children, the largest positive held batch released when the pool is empty.
fn s4_mc(f: &[Vec<f64>], ee: usize, gm: usize, eb: usize, q: usize, dead: bool, n: usize, seed: u64) -> Vec<f64> {
    let mut st = seed | 1;
    let mut rnd = || -> f64 {
        st ^= st << 13;
        st ^= st >> 7;
        st ^= st << 17;
        (st >> 11) as f64 / (1u64 << 53) as f64
    };
    // answers by inversion of the pseudo-law of F^(b, .)
    let mut cdf = vec![vec![1.0f64; gm + 1]; eb + 1];
    for b in 1..=eb {
        let mut run = 0.0f64;
        for g in 0..=gm {
            let fb = (1..=b).map(|k| f[k][g]).fold(1.0f64, f64::min);
            run = run.max(fb);
            cdf[b][g] = run;
        }
    }
    let len = if dead { ee + 1 } else { gm + 2 };
    let mut hist = vec![0.0f64; len];
    for _ in 0..n {
        let (mut pool, mut cnt) = (q, 0usize);
        let mut batch = [0usize; 3];
        let mut rel = [false; 3];
        loop {
            while pool > 0 {
                pool -= 1;
                let d = (rnd() * 4.0) as usize;
                if d == 3 {
                    if !dead {
                        cnt += 1;
                    }
                } else if dead && d == 0 {
                    cnt += 1;
                } else if rel[d] {
                    if rnd() < 1.0 / 3.0 {
                        pool += 1;
                    }
                } else {
                    batch[d] += 1;
                }
            }
            let mut best: Option<usize> = None;
            for c in 0..3 {
                if (dead && c == 0) || rel[c] || batch[c] == 0 {
                    continue;
                }
                if best.map_or(true, |b| batch[c] > batch[b]) {
                    best = Some(c);
                }
            }
            let Some(c) = best else { break };
            rel[c] = true;
            let b = batch[c].min(eb);
            let u = rnd();
            let y = (0..=gm).find(|&g| cdf[b][g] >= u).unwrap_or(gm + 1);
            pool += y;
        }
        hist[cnt.min(len - 1)] += 1.0;
    }
    hist.iter().map(|&h| h / n as f64).collect()
}

struct Lev {
    m: i64,
    f: Vec<Vec<f64>>, // [k][g]
    d: Vec<f64>,      // [k]
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let ee: usize = a[1].parse().unwrap();
    let gm: usize = a[2].parse().unwrap();
    let vm: usize = a[3].parse().unwrap();
    let jm: usize = a[4].parse().unwrap();
    let mmax: i64 = a[5].parse().unwrap();
    let every: i64 = a[6].parse().unwrap();
    let nth: usize = a[7].parse().unwrap();
    assert!(jm <= ee);
    let len = gm + 1; // s = 0..GM
    let lf = lnfact_table(4 * (gm + 3 * ee + 10) + 10);
    let ln4 = 4.0f64.ln();
    let lbin = |n: usize, k: usize| lf[n] - lf[k] - lf[n - k];

    let mut lev = Lev {
        m: -1,
        f: (0..=ee)
            .map(|k| {
                (0..=gm)
                    .map(|g| binom_le(&lf, k, 1.0 / 3.0, g as i64))
                    .collect()
            })
            .collect(),
        d: vec![0.0; ee + 1],
    };
    if a.len() > 10 {
        let m0: i64 = a[8].parse().unwrap();
        let d1: f64 = a[9].parse().unwrap();
        let dinf: f64 = a[10].parse().unwrap();
        let mut d = vec![0.0f64; ee + 1];
        let mut f = vec![vec![1.0f64; gm + 1]; ee + 1];
        // FHAT_ROWS=path (with DELTA1 < 0): full-row seed from a lower law (as the seed of Lemma 13.4 of the
        // paper), the lines "MEAN h k e" and "CDF h k g F" at h = M0: P(G_M0(k) <= g) <= (1 + eps) F and
        // E G_M0(k) >= (1 - eps) e, eps = FHAT_ROWS_EPS (default 0); D(k) is the running minimum over k' <= k of
        // mu_M0(k') - (1 - eps) e_k' (Lemma 10.7 (1)), and the rows enter the cdf minimum below.
        let mut rowf = vec![vec![1.0f64; gm + 1]; ee + 1];
        let mut drow = vec![f64::INFINITY; ee + 1];
        if let Ok(path) = env::var("FHAT_ROWS") {
            let eps: f64 = env::var("FHAT_ROWS_EPS").ok().and_then(|s| s.parse().ok()).unwrap_or(0.0);
            let txt = std::fs::read_to_string(&path).expect("FHAT_ROWS file");
            let mut emean = vec![0.0f64; ee + 1];
            for line in txt.lines() {
                let w: Vec<&str> = line.split_whitespace().collect();
                if w.len() >= 4 && w[0] == "MEAN" && w[1].parse::<i64>().ok() == Some(m0) {
                    let k: usize = w[2].parse().unwrap();
                    if k <= ee { emean[k] = w[3].parse::<f64>().unwrap() * (1.0 - eps); }
                }
                if w.len() >= 5 && w[0] == "CDF" && w[1].parse::<i64>().ok() == Some(m0) {
                    let k: usize = w[2].parse().unwrap();
                    let g: usize = w[3].parse().unwrap();
                    if k <= ee && g <= gm { rowf[k][g] = (w[4].parse::<f64>().unwrap() * (1.0 + eps)).min(1.0); }
                }
            }
            let mut run = f64::INFINITY;
            drow[0] = f64::INFINITY;
            for k in 1..=ee {
                run = run.min(mu(m0, k) - emean[k]);
                drow[k] = run;
            }
            println!("# rows seed from {} at m0 {}, eps {}: D(1) <= {:.6}, D(E) <= {:.6}, F(1, 11) {:.6e}", path, m0, eps, drow[1], drow[ee], rowf[1][11.min(gm)]);
        }
        d[0] = mu(m0, 0);
        for k in 1..=ee {
            // DELTA1 < 0: base from E G(1) alone, D(k) <= D(1) = DELTAINF mu_M0(1) (D nonincreasing in k)
            d[k] = if d1 < 0.0 {
                dinf * mu(m0, 1)
            } else {
                mu(m0, k) * (d1 * 4f64.powi(-(k as i32 - 1)) + dinf)
            };
            if d1 < 0.0 {
                d[k] = d[k].min(drow[k]);
            }
            for g in 0..=gm {
                f[k][g] = binom_le(&lf, k, 1.0 / 3.0, g as i64)
                    .min(defbound(d[k], mu(m0, k), g))
                    .min(f[k - 1][g])
                    .min(rowf[k][g]);
            }
            for g in (0..gm).rev() {
                f[k][g] = f[k][g].min(f[k][g + 1]);
            }
        }
        // DELTA1 <= -2: also a poverty profile P(G(k) <= 31) <= p_k, p = 0.075, 0.019, 0.005, 0.0014
        // (k >= 4: 0.0014), the values P(B(k) < 32) of a floating point probe of a capped model at m = 250,
        // with a 10 percent margin
        // FHAT_POV=g0,p1,p2,p3,p4 replaces the threshold 31 and the values p_1..p_4 (k >= 4: p_4).
        if d1 <= -2.0 {
            let (mut g0, mut p) = (31usize, [1.0, 0.075, 0.019, 0.005, 0.0014]);
            if let Ok(s) = env::var("FHAT_POV") {
                let v: Vec<f64> = s.split(',').map(|x| x.parse().unwrap()).collect();
                g0 = v[0] as usize;
                for i in 1..=4 {
                    p[i] = v[i];
                }
            }
            for k in 1..=ee {
                for g in 0..=g0.min(gm) {
                    f[k][g] = f[k][g].min(p[k.min(4)]);
                }
            }
        }
        lev = Lev { m: m0, f, d };
        println!(
            "# seed m0 {} delta1 {} deltainf {} (hypothetical)",
            m0, d1, dinf
        );
    }
    // FHAT_LOAD=path: start from a state saved by FHAT_SAVE (same E and GM), instead of the seed
    if let Ok(path) = env::var("FHAT_LOAD") {
        let txt = std::fs::read_to_string(&path).unwrap();
        let mut it = txt.split_whitespace();
        let m0: i64 = it.next().unwrap().parse().unwrap();
        let e0: usize = it.next().unwrap().parse().unwrap();
        let g0: usize = it.next().unwrap().parse().unwrap();
        assert!(e0 <= ee && g0 <= gm);
        let mut d = vec![0.0f64; ee + 1];
        let mut f = vec![vec![1.0f64; gm + 1]; ee + 1];
        for k in 0..=e0 {
            d[k] = it.next().unwrap().parse().unwrap();
            for g in 0..=g0 {
                f[k][g] = it.next().unwrap().parse().unwrap();
            }
            // g > G0: the coin and deficit bounds of the saved deficit
            for g in (g0 + 1)..=gm {
                f[k][g] = binom_le(&lf, k, 1.0 / 3.0, g as i64).min(defbound(d[k], mu(m0, k), g));
            }
            for g in (0..gm).rev() {
                f[k][g] = f[k][g].min(f[k][g + 1]);
            }
        }
        // k > E0: G(k) >= G(E0) pathwise and D(k) <= D(E0) (Lemma 10.7 (1) of the paper)
        for k in (e0 + 1)..=ee {
            d[k] = d[e0];
            for g in 0..=gm {
                f[k][g] = f[e0][g]
                    .min(binom_le(&lf, k, 1.0 / 3.0, g as i64))
                    .min(defbound(d[k], mu(m0, k), g));
            }
            for g in (0..gm).rev() {
                f[k][g] = f[k][g].min(f[k][g + 1]);
            }
        }
        lev = Lev { m: m0, f, d };
        println!("# loaded state at height {} from {}", m0, path);
    }
    println!(
        "# fhat E {} GM {} VM {} JM {} MMAX {}",
        ee, gm, vm, jm, mmax
    );
    println!("# m  delta(1) delta(2) delta(4) delta(8) delta(JM) delta(E)  F(1,2) F(1,8) F(1,16) F(2,16) F(4,16) F(8,16)  PB(1,J1) J1  PB(JM,JM)");

    let mmx = 3 * (ee - 1); // largest M
    let fmean = env::var("FHAT_FMEAN").is_ok();
    let spine = env::var("FHAT_SPINE").is_ok();
    // FHAT_SPINE=s2 or s3 keeps one of the two bounds only (an ablation)
    let spine_mode = env::var("FHAT_SPINE").unwrap_or_default();
    let (use_s2, use_s3) = (spine_mode != "s3", spine_mode != "s2");
    let spine_check = env::var("FHAT_SPINE_CHECK").is_ok();
    // FHAT_S4: the S4 release term, not in the paper (deficit rows by S2 with S4 siblings, cdf rows by
    // the S4 ups), batches capped at FHAT_S4E (default E), rows j <= FHAT_S4J (default E); FHAT_S4=d or
    // FHAT_S4=c keeps the deficit or the cdf part only (an ablation); FHAT_S4_CHECK compares the laws with a
    // Monte Carlo of the process.
    let s4 = env::var("FHAT_S4").is_ok();
    let s4_mode = env::var("FHAT_S4").unwrap_or_default();
    let s4e: usize = env::var("FHAT_S4E").ok().map(|s| s.parse().unwrap()).unwrap_or(ee).min(ee);
    let s4j: usize = env::var("FHAT_S4J").ok().map(|s| s.parse().unwrap()).unwrap_or(ee).min(ee);
    let s4_check = env::var("FHAT_S4_CHECK").is_ok();
    // FHAT_S4_MCN: the number of Monte Carlo runs per law in the check (default 1e6)
    let s4n: usize = env::var("FHAT_S4_MCN").ok().map(|s| s.parse().unwrap()).unwrap_or(1_000_000);
    // one step from the state lev (children at every height in [wlo, whi], lev.d[k] / mu_wlo(k)
    // read as the normalized deficit bound at each of them) to the parents at heights
    // [wlo + 1, whi + 1]; returns the cdf bounds valid at all of them, absolute deficits at
    // wlo + 1, the normalized deficits, P_B and the best J. With wlo = whi it is the plain step.
    let step = |lev: &Lev, wlo: i64, whi: i64| -> (Lev, Vec<f64>, Vec<Vec<f64>>, Vec<usize>) {
        let m = lev.m;
        // pseudo-pmfs of the children
        let pm: Vec<Vec<f64>> = lev
            .f
            .iter()
            .map(|fk| {
                (0..=gm)
                    .map(|g| {
                        if g == 0 {
                            fk[0]
                        } else {
                            (fk[g] - fk[g - 1]).max(0.0)
                        }
                    })
                    .collect()
            })
            .collect();
        // Z2[L](s) = sum over ordered (e2, e3), e2 + e3 = L, e2, e3 < E of C(L, e2) (p_e2 * p_e3)(s)
        let mut z2 = vec![vec![0.0f64; len]; 2 * ee - 1];
        for (l, z2l) in z2.iter_mut().enumerate() {
            let lo = if l + 1 > ee { l + 1 - ee } else { 0 };
            for e2 in lo..=l.min(ee - 1) {
                let e3 = l - e2;
                if e2 > e3 {
                    break;
                }
                let w = lbin(l, e2).exp() * if e2 == e3 { 1.0 } else { 2.0 };
                let h = conv(&pm[e2], &pm[e3], len);
                for s in 0..len {
                    z2l[s] += w * h[s];
                }
            }
        }
        // ZB[J][M](s) = sum over e1 < J of C(M, e1) (p_e1 * Z2[M - e1])(s); Z = ZB[E]
        let mut zb = vec![vec![vec![0.0f64; len]; mmx + 1]; ee + 1];
        for e1 in 0..ee {
            let mut cur = zb[e1].clone();
            for (mm, curm) in cur.iter_mut().enumerate().skip(e1) {
                let l = mm - e1;
                if l > 2 * ee - 2 {
                    continue;
                }
                let w = lbin(mm, e1).exp();
                let h = conv(&pm[e1], &z2[l], len);
                for s in 0..len {
                    curm[s] += w * h[s];
                }
            }
            zb[e1 + 1] = cur;
        }
        // sum_M sum_s Psi_M(s) Z_M(s); Psi_M = envelope of C(q + s, M) 4^-(q + s) on
        // max(0, M - q) <= s <= hi_M, hi_M = min(smax, v + M - q) (v = None: no cut)
        let query = |z: &Vec<Vec<f64>>, q: usize, vcut: Option<usize>, smax: usize| -> f64 {
            let mut tot = 0.0;
            for (mm, zm) in z.iter().enumerate() {
                let lo = if mm > q { mm - q } else { 0 };
                let mut hi = smax.min(gm) as i64;
                if let Some(v) = vcut {
                    hi = hi.min(v as i64 + mm as i64 - q as i64);
                }
                if hi < lo as i64 {
                    continue;
                }
                let hi = hi as usize;
                QUERY_OPS.fetch_add(hi as u64 + 1, Relaxed);
                EXP_OPS.fetch_add((hi + 1 - lo) as u64, Relaxed);
                let mut run = 0.0f64;
                for s in (0..=hi).rev() {
                    if s >= lo {
                        let n = q + s;
                        run = run.max((lbin(n, mm) - n as f64 * ln4).exp());
                    }
                    tot += run * zm[s];
                }
            }
            tot
        };
        // independent check (FHAT_CHECK): direct enumeration of the triples e against Z_M
        if env::var("FHAT_CHECK").is_ok() {
            let mut worst = 0.0f64;
            for &(q, vc, smax, jj) in [
                (2usize, Some(0usize), 20usize, ee),
                (2, Some(3), 40, ee),
                (5, Some(8), 60, ee),
                (3, None, 50, 2),
                (6, None, 90, ee.min(5)),
                (9, Some(16), 120, ee),
            ]
            .iter()
            {
                let fast = if vc.is_some() {
                    query(&zb[ee], q, vc, smax)
                } else {
                    query(&zb[jj], q, None, smax)
                };
                let mut slow = 0.0;
                for e1 in 0..(if vc.is_some() { ee } else { jj }) {
                    for e2 in 0..ee {
                        for e3 in 0..ee {
                            let mm = e1 + e2 + e3;
                            let h = conv(&conv(&pm[e1], &pm[e2], len), &pm[e3], len);
                            let lmc = lf[mm] - lf[e1] - lf[e2] - lf[e3];
                            let mut w = vec![0.0f64; len];
                            for s in 0..=smax.min(gm) {
                                let n = q + s;
                                if n < mm {
                                    continue;
                                }
                                if let Some(v) = vc {
                                    if n - mm > v {
                                        continue;
                                    }
                                }
                                w[s] = (lmc + lbin(n, mm) - n as f64 * ln4).exp();
                            }
                            let mut run = 0.0f64;
                            for s in (0..len).rev() {
                                run = run.max(w[s]);
                                slow += run * h[s];
                            }
                        }
                    }
                }
                let rel = (fast - slow).abs() / slow.max(1e-300);
                worst = worst.max(rel);
                println!(
                    "# check m {} q {} v {:?} smax {} J {}: Z_M {:.12e} direct {:.12e}",
                    m, q, vc, smax, jj, fast, slow
                );
            }
            println!("# check m {}: max relative difference {:.3e}", m, worst);
        }
        let fe = &lev.f[ee];
        let ngrid = |q: usize| -> Vec<usize> {
            let mut v: Vec<usize> = [8, 16, 24, 32, 48, 64, 96, 128, 192, 256]
                .iter()
                .map(|x| q + x)
                .filter(|&k| k <= q + gm + 1)
                .collect();
            if v.last() != Some(&(q + gm + 1)) {
                v.push(q + gm + 1);
            }
            v
        };
        let mut pb = vec![vec![1.0f64; jm + 1]; ee + 1];
        let mut fa = vec![vec![1.0f64; vm + 1]; ee + 1];
        std::thread::scope(|sc| {
            let hs: Vec<_> = (0..nth)
                .map(|i| {
                    let (zb, lf, query, ngrid) = (&zb, &lf, &query, &ngrid);
                    sc.spawn(move || {
                        let mut out = Vec::new();
                        for j in (1..=ee).filter(|j| j % nth == i) {
                            let q = j + 1;
                            let mut rb = vec![1.0f64; jm + 1];
                            for (jj, rbj) in rb.iter_mut().enumerate().skip(1) {
                                let nb = 1.0 - binom_le(lf, ee + jj - 1, 0.5, ee as i64 - 1);
                                for &kk in ngrid(q).iter() {
                                    let mut tot = query(&zb[jj], q, None, kk - q - 1);
                                    tot += 2.0 * nb * fe[(kk - q - 1).min(gm)];
                                    tot += binom_le(lf, kk, 0.25, jj as i64 - 1);
                                    *rbj = rbj.min(tot);
                                }
                            }
                            let mut ra = vec![f64::INFINITY; vm + 1]; // raw (A) bound, may exceed 1
                            for (v, rav) in ra.iter_mut().enumerate() {
                                let nb = 1.0 - binom_le(lf, ee + v, 0.5, ee as i64 - 1);
                                for &n0 in ngrid(q).iter() {
                                    let mut tot = query(&zb[ee], q, Some(v), n0 - q - 1);
                                    tot += 3.0 * nb * fe[(n0 - q - 1).min(gm)];
                                    tot += binom_le(lf, n0, 0.25, v as i64);
                                    *rav = rav.min(tot);
                                }
                            }
                            out.push((j, rb, ra));
                        }
                        out
                    })
                })
                .collect();
            for h in hs {
                for (j, rb, ra) in h.join().unwrap() {
                    pb[j] = rb;
                    fa[j] = ra;
                }
            }
        });
        if env::var("FHAT_CDF").is_ok() && wlo == whi && (wlo + 1) % every == 0
            || wlo + 1 < 10 && env::var("FHAT_CDF").is_ok()
        {
            let row: Vec<String> = (0..=5.min(vm))
                .map(|v| format!("{:.4}", fa[1][v]))
                .collect();
            println!(
                "# raw (A) bound at m {} for P(G(1) <= v), v = 0..5: {}",
                wlo + 1,
                row.join(" ")
            );
        }
        // normalized deficits at the parents: worst case over the children's heights wlo, whi
        // (each ratio below is monotone in the height, so its maximum is at an end)
        let dlt: Vec<f64> = (0..=ee).map(|k| lev.d[k] / mu(m, k).max(1e-300)).collect();
        let rmax = |jj: usize, j: usize| -> f64 {
            [wlo, whi]
                .iter()
                .map(|&h| mu(h, jj) / mu(h + 1, j))
                .fold(0.0f64, f64::max)
        };
        let mut dnn = vec![0.0f64; ee + 1];
        let mut jbest = vec![0usize; ee + 1];
        for j in 1..=ee {
            let mut best = [wlo, whi]
                .iter()
                .map(|&h| mu(h, 0) / mu(h + 1, j))
                .fold(0.0f64, f64::max);
            for jj in 1..=jm {
                let p = pb[j][jj].min(1.0);
                let c = (dlt[jj] * (1.0 - p) + p) * rmax(jj, j);
                if c < best {
                    best = c;
                    jbest[j] = jj;
                }
            }
            dnn[j] = best.max(0.0);
        }
        // FHAT_SPINE: the terms of Lemma 12.1 in the step map Phi of Definition 12.3 of the paper. S2:
        // delta'(j) <= sum_k A^j(k)
        // Dt_j(k), Dt_j(k) = min over k' <= k of delta(k') r(k', j), delta(0) = 1, r the worst-end ratio;
        // S3: F'(j, v) <= P(X''_j <= v). Both from F(1, .) of the state.
        let mut s3cdf: Vec<Vec<f64>> = Vec::new();
        if spine {
            let (s2, s3) = spine_laws(&lev.f[1], ee, gm);
            let mut nused = 0usize;
            let (d17, mut ds2) = (dnn[1], f64::INFINITY);
            for j in 1..=ee {
                let mut run = f64::INFINITY;
                let mut tot = 0.0f64;
                for (k, &pk) in s2[j + 1].iter().enumerate() {
                    let dk = if k == 0 { 1.0 } else { dlt[k] };
                    run = run.min(dk * rmax(k, j));
                    tot += pk * run;
                }
                if j == 1 {
                    ds2 = tot;
                }
                if use_s2 && tot < dnn[j] {
                    dnn[j] = tot;
                    jbest[j] = 0;
                    nused += 1;
                }
            }
            s3cdf = (0..=ee)
                .map(|j| {
                    let mut acc = 0.0f64;
                    (0..=gm)
                        .map(|g| {
                            if j >= 1 {
                                acc += s3[j + 1][g];
                            }
                            if j >= 1 { acc.min(1.0) } else { 1.0 }
                        })
                        .collect()
                })
                .collect();
            if spine_check && (wlo != whi || (wlo + 1) % every == 0) {
                let mut r = vec![0.0f64; gm + 2];
                let mut prev = 0.0f64;
                for g in 0..=gm {
                    r[g] = (lev.f[1][g] - prev).max(0.0);
                    prev = prev.max(lev.f[1][g]);
                }
                r[gm + 1] = (1.0 - prev).max(0.0);
                let mut worst = 0.0f64;
                for &q in [2usize, 3, 5, ee + 1].iter() {
                    let a = stage_forward(&r, &[0.25, 3.0 / 11.0, 0.3], &[0.5, 3.0 / 11.0, 0.0], ee, q);
                    let b = stage_forward(&r, &[0.25, 3.0 / 11.0, 0.3, 1.0 / 3.0], &[0.75, 6.0 / 11.0, 0.3, 0.0], gm + 1, q);
                    for k in 0..=ee {
                        worst = worst.max((a[k] - s2[q][k]).abs());
                    }
                    for x in 0..=gm + 1 {
                        worst = worst.max((b[x] - s3[q][x]).abs());
                    }
                }
                println!("# spine check m {}: backward and forward laws differ by at most {:.3e} (q = 2, 3, 5, E + 1)", wlo + 1, worst);
            }
            if wlo != whi || (wlo + 1) % every == 0 || wlo + 1 < 10 {
                println!(
                    "# spine m {} [{}, {}]: S2 below Lemma 17 on {} of {} rows; delta'(1): Lemma 17 {:.5}, S2 {:.5}; S3 P(X''_1 <= 0, 2, 8) {:.4e} {:.4e} {:.4e}",
                    wlo + 1, wlo, whi, nused, ee, d17, ds2, s3cdf[1][0], s3cdf[1][2.min(gm)], s3cdf[1][8.min(gm)]
                );
            }
        }
        // FHAT_S4: delta'(j) <= sum_k P(e*_c = k) Dt_j(k) (S2 with S4 siblings) and F'(j, v) <= P(X*_j <= v)
        // (S4 with three live children), from the rows F(1..EB, .) of the state (terms not in the paper).
        let mut s4cdf: Vec<Vec<f64>> = Vec::new();
        let mut n4d = 0usize;
        if s4 {
            let (lx, le) = s4_laws(&lev.f, ee, gm, s4e, s4j, &lf);
            let mut d4 = f64::NAN;
            if s4_mode != "c" {
                for j in 1..=s4j {
                    let mut run = f64::INFINITY;
                    let mut tot = 0.0f64;
                    for (k, &pk) in le[j + 1].iter().enumerate() {
                        let dk = if k == 0 { 1.0 } else { dlt[k] };
                        run = run.min(dk * rmax(k, j));
                        tot += pk * run;
                    }
                    if j == 1 {
                        d4 = tot;
                    }
                    if tot < dnn[j] {
                        dnn[j] = tot;
                        jbest[j] = 0;
                        n4d += 1;
                    }
                }
            }
            s4cdf = (0..=ee)
                .map(|j| {
                    let mut acc = 0.0f64;
                    (0..=gm)
                        .map(|g| {
                            if j >= 1 && j <= s4j && s4_mode != "d" {
                                acc += lx[j + 1][g];
                                acc.min(1.0)
                            } else {
                                1.0
                            }
                        })
                        .collect()
                })
                .collect();
            if s4_check && (wlo != whi || (wlo + 1) % every == 0) {
                let mut wz = 0.0f64;
                let mut wat = (0usize, false, 0usize, 0.0f64, 0.0f64);
                let mut worst = 0.0f64;
                for &q in [2usize, 3, 6].iter().filter(|&&q| q <= s4j + 1) {
                    for dead in [false, true] {
                        let mc = s4_mc(&lev.f, ee, gm, s4e, q, dead, s4n, 0x9e3779b97f4a7c15 ^ (q as u64) << 8 ^ dead as u64);
                        let law = if dead { &le[q] } else { &lx[q] };
                        let (mut a, mut b) = (0.0f64, 0.0f64);
                        for x in 0..law.len() {
                            a += law[x];
                            b += mc[x];
                            worst = worst.max((a - b).abs());
                            let sd = (b * (1.0 - b)).max(1.0 / s4n as f64).sqrt() / (s4n as f64).sqrt();
                            if b.min(1.0 - b) >= 1e-3 && (a - b).abs() / sd > wz {
                                wz = (a - b).abs() / sd;
                                wat = (q, dead, x, a, b);
                            }
                        }
                    }
                }
                println!("# s4 check m {}: largest cdf difference between s4_laws and a Monte Carlo of {:.0e} runs {:.3e}, largest ratio to the binomial standard error where the Monte Carlo cdf is in [1e-3, 1 - 1e-3] {:.2} at (q, dead, x) = ({}, {}, {}) with cdf {:.6e} against {:.6e} (q = 2, 3, 6, live and dead; cdf points of every law)", wlo + 1, s4n as f64, worst, wz, wat.0, wat.1, wat.2, wat.3, wat.4);
            }
            if wlo != whi || (wlo + 1) % every == 0 || wlo + 1 < 10 {
                let c1 = |v: usize| if s4cdf.len() > 1 { s4cdf[1][v.min(gm)] } else { 1.0 };
                println!(
                    "# s4 m {} [{}, {}]: S2S4 below the other deficit bounds on {} of {} rows; delta'(1) by S2S4 {:.5}; S4 P(X*_1 <= 0, 2, 8) {:.4e} {:.4e} {:.4e}",
                    wlo + 1, wlo, whi, n4d, s4j, d4, c1(0), c1(2), c1(8)
                );
            }
        }
        let mut dn = vec![0.0f64; ee + 1];
        dn[0] = mu(wlo + 1, 0);
        for j in 1..=ee {
            dn[j] = dnn[j] * mu(wlo + 1, j);
        }
        // cdf bounds at the parents (the deficit bounds are weakest at the lowest height)
        let mut fnw = vec![vec![1.0f64; gm + 1]; ee + 1];
        let (mut n3, mut j3, mut g3) = (0usize, 0usize, 0usize); // cdf entries where S3 is the active bound, the largest such j and g
        let mut n4c = 0usize; // cdf entries where S4 is strictly below the other bounds
        for j in 1..=ee {
            let mu1 = mu(wlo + 1, j);
            for g in 0..=gm {
                let mut b = binom_le(&lf, j, 1.0 / 3.0, g as i64);
                b = b.min(defbound(dn[j], mu1, g));
                if g <= vm {
                    b = b.min(fa[j][g]);
                }
                if s4 && s4_mode != "d" && j <= s4j {
                    if s4cdf[j][g] < b.min(fnw[j - 1][g]) {
                        n4c += 1;
                    }
                    b = b.min(s4cdf[j][g]);
                }
                if spine && use_s3 {
                    if s3cdf[j][g] < b.min(fnw[j - 1][g]) {
                        n3 += 1;
                        j3 = j3.max(j);
                        g3 = g3.max(g);
                    }
                    b = b.min(s3cdf[j][g]);
                }
                b = b.min(fnw[j - 1][g]);
                fnw[j][g] = b;
            }
            for g in (0..gm).rev() {
                fnw[j][g] = fnw[j][g].min(fnw[j][g + 1]);
            }
        }
        if spine && use_s3 && (wlo != whi || (wlo + 1) % every == 0 || wlo + 1 < 10) {
            println!("# spine m {}: S3 active on {} cdf entries, largest j {} and g {}", wlo + 1, n3, j3, g3);
        }
        if s4 && (wlo != whi || (wlo + 1) % every == 0 || wlo + 1 < 10) {
            println!("# s4 m {}: S4 strictly below the other cdf bounds on {} entries (before the monotonizations)", wlo + 1, n4c);
        }
        // FHAT_FMEAN: deficits from the cdf bounds, E G(j) >= sum over g <= GM of (1 - F'(j, g)), so
        // Delta(j) <= mu(j) - that sum (normalized at the highest parent height, where it is largest),
        // and Delta(j) <= Delta(k) for k < j (Lemma 10.7 (1) of the paper); then the deficit cdf bounds are
        // redone.
        if fmean {
            for _round in 0..2 {
                for j in 1..=ee {
                    let s: f64 = fnw[j].iter().map(|&x| 1.0 - x).sum();
                    dnn[j] = dnn[j].min((1.0 - s / mu(whi + 1, j)).max(0.0));
                    dn[j] = dnn[j] * mu(wlo + 1, j);
                    if j > 1 && dn[j] > dn[j - 1] {
                        dn[j] = dn[j - 1];
                        dnn[j] = dn[j] / mu(wlo + 1, j);
                    }
                }
                for j in 1..=ee {
                    let mu1 = mu(wlo + 1, j);
                    for g in 0..=gm {
                        fnw[j][g] = fnw[j][g].min(defbound(dn[j], mu1, g)).min(fnw[j - 1][g]);
                    }
                    for g in (0..gm).rev() {
                        fnw[j][g] = fnw[j][g].min(fnw[j][g + 1]);
                    }
                }
            }
        }
        (
            Lev {
                m: wlo + 1,
                f: fnw,
                d: dn,
            },
            dnn,
            pb,
            jbest,
        )
    };

    // optional supersolution check: ... ML MH ETA after the seed arguments
    let floor: f64 = if a.len() > 14 {
        a[14].parse().unwrap()
    } else {
        0.0
    };
    let check: Option<(i64, i64, f64)> = if a.len() > 13 {
        Some((
            a[11].parse().unwrap(),
            a[12].parse().unwrap(),
            a[13].parse().unwrap(),
        ))
    } else {
        None
    };
    let mstop = check.map(|c| c.0).unwrap_or(mmax);
    while lev.m < mstop {
        let (nl, _dnn, pb, jbest) = step(&lev, lev.m, lev.m);
        if env::var("FHAT_OPS").is_ok() {
            let (c, q, x) = (
                CONV_OPS.swap(0, Relaxed),
                QUERY_OPS.swap(0, Relaxed),
                EXP_OPS.swap(0, Relaxed),
            );
            println!("# ops at m {}: convolution multiply-adds {:.3e}, query terms {:.3e}, query exponentials {:.3e}", nl.m, c as f64, q as f64, x as f64);
            if spine {
                println!("# spine ops at m {}: multiply-adds in the S2 and S3 laws {:.3e}", nl.m, SPINE_OPS.swap(0, Relaxed) as f64);
            }
            if s4 {
                println!("# s4 ops at m {}: multiply-adds in the S4 laws {:.3e}", nl.m, S4_OPS.swap(0, Relaxed) as f64);
            }
        }
        lev = nl;
        // FHAT_SAVEAT=h1,h2,... with FHAT_SAVEDIR=dir: also write the state at those heights to dir/m<h>.st
        if let (Ok(at), Ok(dir)) = (env::var("FHAT_SAVEAT"), env::var("FHAT_SAVEDIR")) {
            if at.split(',').any(|h| h.parse::<i64>().ok() == Some(lev.m)) {
                save_state(&lev, ee, gm, &format!("{}/m{}.st", dir, lev.m));
            }
        }
        let m1 = lev.m;
        if env::var("FHAT_CDF").is_ok() && (m1 % every == 0 || m1 == mstop || m1 < 10) {
            // F(k, g) for k = 1, 2, 4 and g = 0..11, and the cdf mean sum_g (1 - F(1, g)) / mu(1)
            for k in [1usize, 2, 4].iter().filter(|&&k| k <= ee) {
                let row: Vec<String> = (0..=11.min(gm))
                    .map(|g| format!("{:.4}", lev.f[*k][g]))
                    .collect();
                let s: f64 = lev.f[*k].iter().map(|&x| 1.0 - x).sum();
                println!(
                    "# cdf m {} k {}: {} | sum (1 - F) {:.4} mu {:.4}",
                    m1,
                    k,
                    row.join(" "),
                    s,
                    mu(m1, *k)
                );
            }
        }
        if m1 % every == 0 || m1 == mstop || m1 < 10 {
            let dl = |k: usize| lev.d[k.min(ee)] / mu(m1, k.min(ee));
            let fg = |k: usize, g: usize| lev.f[k.min(ee)][g.min(gm)];
            println!(
                "{} {:.5} {:.5} {:.5} {:.5} {:.5} {:.5}  {:.3e} {:.3e} {:.3e} {:.3e} {:.3e} {:.3e}  {:.3e} {} {:.3e}",
                m1,
                dl(1),
                dl(2),
                dl(4),
                dl(8),
                dl(jm),
                dl(ee),
                fg(1, 2),
                fg(1, 8),
                fg(1, 16),
                fg(2, 16),
                fg(4, 16),
                fg(8, 16),
                pb[1][jbest[1].max(1)],
                jbest[1],
                pb[jm][jm]
            );
        }
    }
    // FHAT_SAVE=path: write the state reached (before any check)
    if let Ok(path) = env::var("FHAT_SAVE") {
        save_state(&lev, ee, gm, &path);
    }
    if let Some((ml, mh, eta)) = check {
        // S0 = the state at ML inflated by 1 + ETA plus FLOOR on the cdf bounds. Kleene iteration
        // T(0) = S0, T(n+1) = max(T(n), (1 + KETA) Phi_worst(T(n)) + FLOOR) (KETA = FHAT_KETA, default 0), Phi_worst = one worst-case
        // step for children heights ML..MH-1; it stops at the first n with Phi_worst(T(n)) <= T(n)
        // componentwise (PASS: T(n) >= S0 is a supersolution on [ML, MH], Lemma 12.5 (4) of the paper) or after
        // FHAT_NIT iterations (FAIL). FHAT_NIT=1 is the plain check of S0.
        let nit: usize = env::var("FHAT_NIT")
            .ok()
            .map(|s| s.parse().unwrap())
            .unwrap_or(1);
        let keta: f64 = env::var("FHAT_KETA")
            .ok()
            .map(|s| s.parse().unwrap())
            .unwrap_or(0.0);
        let bell: Option<f64> = env::var("FHAT_BELL").ok().map(|s| s.parse().unwrap());
        // FHAT_MARGIN=phi_f,phi_d: absorbing margins for a directed-rounding replay. The search adds
        // phi_f to every cdf update and phi_d to every deficit update (and to the Bellman costs), and
        // PASS requires Phi_worst(T) + margin <= T on every component below its trivial value 1.
        let (phf, phd): (f64, f64) = env::var("FHAT_MARGIN")
            .ok()
            .map(|s| {
                let v: Vec<f64> = s.split(',').map(|x| x.parse().unwrap()).collect();
                (v[0], v[1])
            })
            .unwrap_or((0.0, 0.0));
        // FHAT_KAPPA=kappa: a strict relative margin. PASS also requires (1 + kappa) Phi_worst(T) <= T on every
        // component of T below 1; the Kleene updates are inflated by 1 + kappa and the Bellman system is
        // solved for (1 + kappa) times the operator.
        let kappa: f64 = env::var("FHAT_KAPPA")
            .ok()
            .map(|s| s.parse().unwrap())
            .unwrap_or(0.0);
        let keta = keta.max(kappa);
        let mut tf: Vec<Vec<f64>> = lev
            .f
            .iter()
            .map(|fk| {
                fk.iter()
                    .map(|&x| (x * (1.0 + eta) + floor).min(1.0))
                    .collect()
            })
            .collect();
        let mut td: Vec<f64> = (0..=ee)
            .map(|k| {
                if k == 0 {
                    1.0
                } else {
                    (1.0 + eta) * lev.d[k] / mu(ml, k)
                }
            })
            .collect();
        let k44 = 44.min(ee);
        let td0 = td.clone();
        for it in 0..nit {
            let sl = Lev {
                m: ml,
                f: tf.clone(),
                d: (0..=ee).map(|k| td[k] * mu(ml, k)).collect(),
            };
            let (nl, dnn, pb, jbest) = step(&sl, ml, mh - 1);
            if env::var("FHAT_OPS").is_ok() {
                let (c, q, x) = (
                    CONV_OPS.swap(0, Relaxed),
                    QUERY_OPS.swap(0, Relaxed),
                    EXP_OPS.swap(0, Relaxed),
                );
                println!("# ops at m {}: convolution multiply-adds {:.3e}, query terms {:.3e}, query exponentials {:.3e}", nl.m, c as f64, q as f64, x as f64);
                if spine {
                    println!("# spine ops at m {}: multiply-adds in the S2 and S3 laws {:.3e}", nl.m, SPINE_OPS.swap(0, Relaxed) as f64);
                }
                if s4 {
                    println!("# s4 ops at m {}: multiply-adds in the S4 laws {:.3e}", nl.m, S4_OPS.swap(0, Relaxed) as f64);
                }
            }
            let mut fratio = 0.0f64;
            let mut fat = (0usize, 0usize);
            for k in 1..=ee {
                for g in 0..=gm {
                    if nl.f[k][g] > 0.0 {
                        let r = nl.f[k][g] / tf[k][g].max(1e-300);
                        if r > fratio {
                            fratio = r;
                            fat = (k, g);
                        }
                    }
                }
            }
            let mut dratio = 0.0f64;
            let mut dat = 0usize;
            for k in 1..=ee {
                let r = dnn[k] / td[k];
                if r > dratio {
                    dratio = r;
                    dat = k;
                }
            }
            // smallest slack T - Phi_worst(T) over the components below 1
            let mut fslack = f64::INFINITY;
            let mut dslack = f64::INFINITY;
            for k in 1..=ee {
                for g in 0..=gm {
                    if tf[k][g] < 1.0 {
                        fslack = fslack.min(tf[k][g] - nl.f[k][g]);
                    }
                }
                if td[k] < 1.0 {
                    dslack = dslack.min(td[k] - dnn[k]);
                }
            }
            // largest ratios over the components below 1, for the relative margin
            let mut frel = 0.0f64;
            let mut drel = 0.0f64;
            for k in 1..=ee {
                for g in 0..=gm {
                    if tf[k][g] < 1.0 {
                        frel = frel.max(nl.f[k][g] / tf[k][g].max(1e-300));
                    }
                }
                if td[k] < 1.0 {
                    drel = drel.max(dnn[k] / td[k]);
                }
            }
            let pass = fratio <= 1.0
                && dratio <= 1.0
                && fslack >= phf
                && dslack >= phd
                && (1.0 + kappa) * frel <= 1.0
                && (1.0 + kappa) * drel <= 1.0;
            if kappa > 0.0 {
                println!("# relative margin at iteration {}: max (1 + kappa) F'/T = {:.12}, max (1 + kappa) delta'/delta_T = {:.12} over the components below 1 (kappa {:.1e})", it, (1.0 + kappa) * frel, (1.0 + kappa) * drel, kappa);
            }
            if phf > 0.0 || phd > 0.0 {
                println!("# margins at iteration {}: smallest cdf slack {:.3e} (required {:.1e}), smallest deficit slack {:.3e} (required {:.1e})", it, fslack, phf, dslack, phd);
            }
            if it + 1 == nit || pass || it % 10 == 0 {
                println!(
                    "# supersolution [{}, {}] eta {} floor {} iteration {}: max F'/T = {:.6} at (k, g) = ({}, {}), max delta'/delta_T = {:.6} at k = {} (J {}, P_B {:.3e}); delta_T(1) {:.5}, delta_T(JM) {:.5}, delta_T(44 or E) {:.5}, P_B(JM, JM) {:.3e}, F_T(1, 16) {:.3e}, F_T(4, 16) {:.3e}, F_T(E, GM) {:.3e}: {}",
                    ml, mh, eta, floor, it, fratio, fat.0, fat.1, dratio, dat, jbest[dat], pb[dat][jbest[dat].max(1)],
                    td[1], td[jm], td[k44], pb[jm][jm], tf[1][16.min(gm)], tf[4.min(ee)][16.min(gm)], tf[ee][gm],
                    if pass { "PASS" } else if it + 1 == nit { "FAIL" } else { "continue" }
                );
            }
            if (pass || it + 1 == nit) && env::var("FHAT_PBTAB").is_ok() {
                for j in [1usize, 2, 4, 8, 12, 16, 24, 32, 48, 64, 96]
                    .iter()
                    .filter(|&&j| j <= ee)
                {
                    let row: Vec<String> =
                        (1..=jm).map(|jj| format!("{:.2e}", pb[*j][jj])).collect();
                    println!("# P_B({}, J) for J = 1..JM: {}", j, row.join(" "));
                }
            }
            // FHAT_SAVET=path: write T (normalized deficits, shortest round-trip decimals) for the
            // outward-rounded check of code/d3cert/cert (d3-cert tcheck), after a PASS or at the last iteration
            // (that check is the judge, so a T that misses d3-fhat's margin test by rounding is still usable):
            // "ML E GM", then per k = 0..E the line delta_T(k) F_T(k, 0..GM)
            if pass || it + 1 == nit {
                if let Ok(path) = env::var("FHAT_SAVET") {
                    let mut o = format!("{} {} {}\n", ml, ee, gm);
                    for k in 0..=ee {
                        o.push_str(&format!("{:e}", td[k]));
                        for g in 0..=gm {
                            o.push_str(&format!(" {:e}", tf[k][g]));
                        }
                        o.push('\n');
                    }
                    std::fs::write(&path, o).unwrap();
                    println!("# FHAT_SAVET: T of iteration {} written to {} ({})", it, path, if pass { "PASS" } else { "FAIL" });
                }
            }
            if pass {
                println!(
                    "# hand-over to Theorem D' (row 0.85, 0.01: delta(1) <= 0.15, delta(44) <= 0.042955 = 1 - b1/mu_m1(44) rounded down, b1 = 100895.78, with delta(44) <= delta(E) if E < 44): delta_T(1) {:.5}, delta_T(44 or E) {:.5}: {}",
                    td[1], td[k44], if td[1] <= 0.15 && td[k44] <= 0.042955 { "MET" } else { "NOT MET" }
                );
                // FHAT_HROWS=a1,b1,J1;a2,b2,J2;...: the same test against other rows of Theorem 14.1 of the paper
                // (delta_T(1) <= a, delta_T(J) <= b, with delta_T(E) for delta_T(J) when E < J); the
                // thresholds are the caller's, the interval [ML, MH] must end at that row's m1
                if let Ok(rows) = env::var("FHAT_HROWS") {
                    for r in rows.split(';').filter(|s| !s.trim().is_empty()) {
                        let v: Vec<f64> = r.split(',').map(|s| s.trim().parse().unwrap()).collect();
                        let (a1, b1, jj) = (v[0], v[1], v[2] as usize);
                        let kj = jj.min(ee);
                        println!(
                            "# hand-over row (delta(1) <= {}, delta({}) <= {}) on [{}, {}]{}: delta_T(1) {:.5}, delta_T({}) {:.5}: {}",
                            a1, jj, b1, ml, mh, if kj < jj { " (E < J, delta_T(E) used)" } else { "" },
                            td[1], kj, td[kj], if td[1] <= a1 && td[kj] <= b1 { "MET" } else { "NOT MET" }
                        );
                    }
                }
                break;
            }
            // FHAT_BELL=beta: the deficit part is solved directly. For the current P_B the map
            // delta -> delta' is the Bellman operator of val(j) = min(c0(j), min_J a val(J) + b),
            // a = r (1 - P_B), b = r P_B, r the worst-end ratio; its least fixed point delta* is
            // found by policy iteration as the solution above delta_T(0) of val = max(delta_T(0), Bellman(val)),
            // and delta_T is raised to (1 + beta) val (once per value of val, so it does not grow by itself). Then Bellman(delta_T) <= delta_T at this P_B, since
            // Bellman((1 + beta) v) <= (1 + beta) Bellman(v) (b >= 0) and Bellman(val) <= val.
            let mut dbell: Option<Vec<f64>> = None;
            if let Some(beta) = bell {
                let rr = |jj: usize, j: usize| -> f64 {
                    [ml, mh - 1]
                        .iter()
                        .map(|&h| mu(h, jj) / mu(h + 1, j))
                        .fold(0.0f64, f64::max)
                };
                let c0: Vec<f64> = (0..=ee)
                    .map(|j| {
                        if j == 0 {
                            1.0
                        } else {
                            (1.0 + kappa) * rr(0, j) + phd
                        }
                    })
                    .collect();
                let mut aa = vec![vec![0.0f64; jm + 1]; ee + 1];
                let mut bb = vec![vec![0.0f64; jm + 1]; ee + 1];
                for j in 1..=ee {
                    for jj in 1..=jm {
                        let p = pb[j][jj].min(1.0);
                        aa[j][jj] = (1.0 + kappa) * rr(jj, j) * (1.0 - p);
                        bb[j][jj] = (1.0 + kappa) * rr(jj, j) * p + phd;
                    }
                }
                let (val, pol, pit) = bellman(&aa, &bb, &c0, &td0, jm);
                if it % 10 == 0 || it + 1 == nit {
                    println!(
                        "# Bellman iteration {}: {} policy steps, delta*(1) {:.6}, delta*(JM) {:.6}, delta*(E) {:.6}, policy at 1, JM, E: {} {} {}",
                        it, pit, val[1], val[jm], val[ee], pol[1], pol[jm], pol[ee]
                    );
                }
                dbell = Some(val.iter().map(|&v| v * (1.0 + beta)).collect());
            }
            for k in 1..=ee {
                for g in 0..=gm {
                    tf[k][g] = tf[k][g].max((nl.f[k][g] * (1.0 + keta) + floor + phf).min(1.0));
                }
                td[k] = td[k].max((dnn[k] * (1.0 + keta) + phd).min(1.0));
                if let Some(db) = &dbell {
                    td[k] = td[k].max(db[k].min(1.0));
                }
            }
        }
    }
}
