// The root chain in floating point (not a certificate): for a law H of the class, its child chain
// and H* = (1 - eps) H + eps (tail atoms Z_t = (t, ..., t), t = T + 1 + Geom(rho)), the output law
// of the root chain with its full joint law (out prefix). Stopping rule: a state goes to the
// overflow when e > T, when p > pmax, or when its mass is below `tiny`.

use crate::cls::D;
use crate::fx::Map as HashMap;

fn sort4(mut c: [u16; D]) -> [u16; D] {
    c.sort_unstable();
    c
}

pub struct Pot {
    pub phi: f64,
    pub theta: f64,
    pub rho: f64,
    pub m: f64,
    pub w: Vec<f64>, // weight per child state id (see ids below)
}

// packed DP key: 4 child ids (7 bits each), e (5 bits), p (7 bits), out prefix (5 x 4 bits)
#[inline]
fn enc(ch: &[u16; D], e: u32, p: u32, o: &[u8; 6]) -> u64 {
    let mut k = 0u64;
    for c in ch {
        k = (k << 7) | (*c as u64);
    }
    k = (k << 5) | e as u64;
    k = (k << 7) | p as u64;
    for x in o.iter().take(5) {
        k = (k << 4) | (*x as u64);
    }
    k
}
#[inline]
fn dec(mut k: u64) -> ([u16; D], u32, u32, [u8; 6]) {
    let mut o = [0u8; 6];
    for i in (0..5).rev() {
        o[i] = (k & 15) as u8;
        k >>= 4;
    }
    let p = (k & 127) as u32;
    k >>= 7;
    let e = (k & 31) as u32;
    k >>= 5;
    let mut ch = [0u16; D];
    for i in (0..D).rev() {
        ch[i] = (k & 127) as u16;
        k >>= 7;
    }
    (ch, e, p, o)
}

pub const NP: usize = 4;

// For a child chain with ids 0 = F, 1 = boundary, 2..nid the labeled states, then the tail states
// nid + q - 1, q = 1..J-1 (a tail atom with q indices used): returns (joint law of the absorbed
// part, m_ov, S_ov, max live).
pub fn phi_joint_chain(
    mut chain: Vec<Vec<(f64, u8, u16)>>,
    nid: usize,
    j: usize,
    t: usize,
    eps: f64,
    pmax: usize,
    tiny: f64,
    pts: &[Pot],
) -> (HashMap<Vec<u8>, f64>, f64, [f64; NP], usize) {
    assert!(pts.len() <= NP);
    let nst = nid + j - 1;
    assert!(j <= 5 && t <= 15 && pmax <= 127 && nst <= 128);
    let tid = |q: usize| -> u16 { if q == j { 1 } else { (nid + q - 1) as u16 } };
    chain.resize(nst, Vec::new());
    for s in 0..2 {
        for x in chain[s].iter_mut() {
            x.0 *= 1.0 - eps;
        }
    }
    for q in 1..j {
        chain[tid(q) as usize] = vec![(1.0, 0u8, tid(q + 1))];
    }
    let rho = pts[0].rho;
    let phi_of = |ch: &[u16; D], e: u32, p: u32, i: usize| -> [f64; NP] {
        let mut r = [0.0; NP];
        for (k, pt) in pts.iter().enumerate() {
            let mut x = pt.theta.powi(e as i32) * pt.phi.powi((p + (j - i) as u32) as i32);
            for c in ch {
                x *= pt.w[*c as usize];
            }
            r[k] = x;
        }
        r
    };
    let addv = |s: &mut [f64; NP], m: f64, v: [f64; NP]| {
        for k in 0..NP {
            s[k] += m * v[k];
        }
    };
    let mut m_ov = 0.0;
    // m_ov by cause: mass below tiny, e > T, p > pmax, tail-atom deliveries beyond pmax
    let mut mc = [0.0f64; 4];
    // S_ov of the first potential by the same causes
    let mut sc = [0.0f64; 4];
    let mut s_ov = [0.0f64; NP];
    let mut maxlive = 0;
    // frog-boundary states: p = 0
    let mut start: HashMap<u64, f64> = HashMap::default();
    start.insert(enc(&[0; D], 0, 0, &[0; 6]), 1.0);
    for i in 1..=j {
        // the dynamics does not read the output prefix (low 20 bits of the key), so the start
        // states are processed one prefix group after another: memory is that of the largest group
        let mut groups: HashMap<u64, Vec<(u64, f64)>> = HashMap::default();
        for (k, m) in start.drain() {
            let (ch, e, _, o) = dec(k);
            groups.entry(k & 0xFFFFF).or_default().push((enc(&ch, e, 1, &o), m));
        }
        let mut newstart: HashMap<u64, f64> = HashMap::default();
        for (_, g) in groups.drain() {
        let mut pend: HashMap<u64, f64> = HashMap::default();
        for (k, m) in g {
            *pend.entry(k).or_insert(0.0) += m;
        }
        let mut fin: HashMap<u64, f64> = HashMap::default();
        while !pend.is_empty() {
            maxlive = maxlive.max(pend.len());
            let mut next: HashMap<u64, f64> = HashMap::with_capacity_and_hasher(pend.len(), Default::default());
            for (k, m) in pend.drain() {
                let (ch, e, p, o) = dec(k);
                if m < tiny {
                    m_ov += m;
                    mc[0] += m;
                    let v = phi_of(&ch, e, p, i);
                    sc[0] += m * v[0];
                    addv(&mut s_ov, m, v);
                    continue;
                }
                let w = m / (D as f64 + 1.0);
                if e as usize + 1 > t {
                    m_ov += w;
                    mc[1] += w;
                    let v = phi_of(&ch, e + 1, p - 1, i);
                    sc[1] += w * v[0];
                    addv(&mut s_ov, w, v);
                } else if p == 1 {
                    *fin.entry(enc(&ch, e + 1, 0, &o)).or_insert(0.0) += w;
                } else {
                    *next.entry(enc(&ch, e + 1, p - 1, &o)).or_insert(0.0) += w;
                }
                for c in 0..D {
                    if c > 0 && ch[c] == ch[c - 1] {
                        continue;
                    }
                    let mult = ch.iter().filter(|&&x| x == ch[c]).count() as f64;
                    let cs = ch[c] as usize;
                    let push = |nx: u16, dl: usize, mass: f64, next: &mut HashMap<u64, f64>, fin: &mut HashMap<u64, f64>, m_ov: &mut f64, mc: &mut [f64; 4], sc: &mut [f64; 4], s_ov: &mut [f64; NP]| {
                        let np = p as usize - 1 + dl;
                        let mut c2 = ch;
                        c2[c] = nx;
                        let c2 = sort4(c2);
                        if np > pmax {
                            *m_ov += mass;
                            mc[2] += mass;
                            let v = phi_of(&c2, e, np as u32, i);
                            sc[2] += mass * v[0];
                            addv(s_ov, mass, v);
                        } else if np == 0 {
                            *fin.entry(enc(&c2, e, 0, &o)).or_insert(0.0) += mass;
                        } else {
                            *next.entry(enc(&c2, e, np as u32, &o)).or_insert(0.0) += mass;
                        }
                    };
                    for &(pr, dl, nx) in &chain[cs] {
                        push(nx, dl as usize, w * pr * mult, &mut next, &mut fin, &mut m_ov, &mut mc, &mut sc, &mut s_ov);
                    }
                    if cs < 2 {
                        let q0 = if cs == 0 { 2 } else { 1 };
                        let nx = tid(q0);
                        let base = w * eps * mult;
                        let tmax = (pmax + 1).saturating_sub(p as usize);
                        for tt in (t + 1)..=tmax.max(t) {
                            let pr = (1.0 - rho) * rho.powi((tt - t - 1) as i32);
                            push(nx, tt, base * pr, &mut next, &mut fin, &mut m_ov, &mut mc, &mut sc, &mut s_ov);
                        }
                        let t1 = tmax.max(t) + 1;
                        let mass = base * rho.powi((t1 - t - 1) as i32);
                        let mut c2 = ch;
                        c2[c] = nx;
                        let c2 = sort4(c2);
                        m_ov += mass;
                        mc[3] += mass;
                        let v = phi_of(&c2, e, p - 1, i);
                        for (k, pt) in pts.iter().enumerate() {
                            let wsum = base * (1.0 - rho) * rho.powi((t1 - t - 1) as i32) * pt.phi.powi(t1 as i32) / (1.0 - pt.phi * rho);
                            s_ov[k] += wsum * v[k];
                            if k == 0 {
                                sc[3] += wsum * v[k];
                            }
                        }
                    }
                }
            }
            pend = next;
        }
        for (k, m) in fin.drain() {
            let (ch, e, _, mut o) = dec(k);
            o[i - 1] = e as u8;
            *newstart.entry(enc(&ch, e, 0, &o)).or_insert(0.0) += m;
        }
        }
        start = newstart;
    }
    let mut out: HashMap<Vec<u8>, f64> = HashMap::default();
    for (k, m) in start {
        let (_, _, _, o) = dec(k);
        *out.entry(o[..j].to_vec()).or_insert(0.0) += m;
    }
    eprintln!("  m_ov by cause: tiny {:.3e}, e > T {:.3e}, p > pmax {:.3e}, tail deliveries beyond pmax {:.3e}; S_ov (first phi) by cause: {:.3e} {:.3e} {:.3e} {:.3e}", mc[0], mc[1], mc[2], mc[3], sc[0], sc[1], sc[2], sc[3]);
    (out, m_ov, s_ov, maxlive)
}
