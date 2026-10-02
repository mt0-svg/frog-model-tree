// The occupations that choose the flags of the certificate (Section 7 of the paper): the root chain
// of Section 6 on a version 3 table (code/certificate/FORMAT.md), without lumping, in floating
// point, with the stopping rule e > T, p > T', mass below the threshold. Writes, for each phase,
// the pairs (multiset of child states, number of waiting frogs) whose expected number of visits is
// at least XDP_HEAVY_TAU, to the file XDP_HEAVY_OUT (lines "phase key occupation"), and prints
// counts of the run.
// Usage: occupations TABLE.v3 THRESHOLD
mod fx;
use fx::{Fx, Map};
use std::collections::HashSet;
use std::hash::BuildHasherDefault;
type Set = HashSet<u64, BuildHasherDefault<Fx>>;

const D: usize = 4;

fn rat(s: &str) -> f64 {
    match s.split_once('/') {
        Some((a, b)) => a.parse::<f64>().unwrap() / b.parse::<f64>().unwrap(),
        None => s.parse().unwrap(),
    }
}

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
fn sort4(mut c: [u16; D]) -> [u16; D] {
    c.sort_unstable();
    c
}

struct Tab {
    j: usize,
    t: usize,
    tp: usize,
    eps: f64,
    rho: f64,
    phi: f64,
    kappa: f64,
    // rows[q]: (from, delta, to, p)
    rows: Vec<Vec<(String, usize, String, f64)>>,
    labels: Vec<Vec<String>>,
}

fn read_tab(path: &str) -> Tab {
    let s = std::fs::read_to_string(path).unwrap();
    let mut tb = Tab { j: 0, t: 0, tp: 0, eps: 0.0, rho: 0.0, phi: 0.0, kappa: 0.0, rows: Vec::new(), labels: Vec::new() };
    let mut trs = Vec::new();
    let mut labs = Vec::new();
    for l in s.lines() {
        let w: Vec<&str> = l.split_whitespace().collect();
        if w.is_empty() || w[0].starts_with('#') {
            continue;
        }
        match w[0] {
            "J" => tb.j = w[1].parse().unwrap(),
            "T" => tb.t = w[1].parse().unwrap(),
            "Tpend" => tb.tp = w[1].parse().unwrap(),
            "eps" => tb.eps = rat(w[1]),
            "rho" => tb.rho = rat(w[1]),
            "phi" => tb.phi = rat(w[1]),
            "kappa" => tb.kappa = rat(w[1]),
            "label" => labs.push((w[1].parse::<usize>().unwrap(), w[2].to_string())),
            "tr" => trs.push((w[1].parse::<usize>().unwrap(), w[2].to_string(), w[3].parse::<usize>().unwrap(), w[4].to_string(), rat(w[5]))),
            _ => {}
        }
    }
    tb.rows = vec![Vec::new(); tb.j];
    tb.labels = vec![Vec::new(); tb.j];
    for (q, n) in labs {
        tb.labels[q].push(n);
    }
    for (q, a, d, b, p) in trs {
        tb.rows[q].push((a, d, b, p));
    }
    tb
}

struct Chain {
    nst: usize,
    rows: Vec<Vec<(f64, u8, u16)>>, // F and B rows already carry the factor 1 - eps; tails apart
    tid: Vec<u16>, // tid[q] = tail state with q indices used (q = 1..J-1); tid[J] = boundary
}

fn build(tb: &Tab) -> Chain {
    let j = tb.j;
    let mut names = vec!["F".to_string(), "B".to_string()];
    let mut idx: Map<(usize, String), u16> = Map::default();
    for q in 1..j {
        for l in &tb.labels[q] {
            idx.insert((q, l.clone()), names.len() as u16);
            names.push(format!("{}:{}", q, l));
        }
    }
    let mut tid = vec![0u16; j + 1];
    for q in 1..j {
        tid[q] = names.len() as u16;
        names.push(format!("{}:tail", q));
    }
    tid[j] = 1;
    let mut mid = vec![0u16; j + 1];
    for q in 1..j {
        mid[q] = names.len() as u16;
        names.push(format!("{}:M", q));
    }
    mid[j] = 1;
    // max chains of the flag groups (labels with f1: every increment so far <= 1)
    let mut mid0 = vec![0u16; j + 1];
    let mut mid1 = vec![0u16; j + 1];
    for q in 1..j {
        mid0[q] = names.len() as u16;
        names.push(format!("{}:M0", q));
        mid1[q] = names.len() as u16;
        names.push(format!("{}:M1", q));
    }
    mid0[j] = 1;
    mid1[j] = 1;
    let nst = names.len();
    assert!(nst <= 128);
    let id = |q: usize, l: &str| -> u16 { if q == j { 1 } else { idx[&(q, l.to_string())] } };
    let mut rows: Vec<Vec<(f64, u8, u16)>> = vec![Vec::new(); nst];
    let root: Vec<&(String, usize, String, f64)> = tb.rows[0].iter().collect();
    for r in &root {
        rows[1].push(((1.0 - tb.eps) * r.3, r.1 as u8, id(1, &r.2)));
        for r2 in tb.rows[1].iter().filter(|x| x.0 == r.2) {
            rows[0].push(((1.0 - tb.eps) * r.3 * r2.3, (r.1 + r2.1) as u8, id(2, &r2.2)));
        }
    }
    for q in 1..j {
        for r in &tb.rows[q] {
            rows[id(q, &r.0) as usize].push((r.3, r.1 as u8, id(q + 1, &r.2)));
        }
        rows[tid[q] as usize] = vec![(1.0, 0, tid[q + 1])];
        // max chains: pointwise maximum of the tails of the rows of a group of labels of level q.
        // Group all: next M_{q+1}. Flag 0: the flag stays 0, next M0_{q+1}. Flag 1: next M1_{q+1}
        // if the increment is <= 1 (then the real increment is <= 1 too and the real flag stays 1),
        // else M_{q+1}.
        let dmax = tb.rows[q].iter().map(|r| r.1).max().unwrap();
        for sel in 0..3 {
            let mut tmax = vec![0.0f64; dmax + 2];
            for l in tb.labels[q].iter().filter(|l| match sel { 0 => true, 1 => !l.contains("f1"), _ => l.contains("f1") }) {
                let mut tl = vec![0.0f64; dmax + 2];
                for r in tb.rows[q].iter().filter(|r| &r.0 == l) {
                    for k in 0..=r.1 {
                        tl[k] += r.3;
                    }
                }
                for k in 0..=dmax {
                    tmax[k] = tmax[k].max(tl[k]);
                }
            }
            tmax[0] = 1.0;
            let g = [mid[q], mid0[q], mid1[q]][sel] as usize;
            for k in 0..=dmax {
                let pk = tmax[k] - tmax[k + 1];
                if pk > 0.0 {
                    let nx = match sel { 0 => mid[q + 1], 1 => mid0[q + 1], _ => if k <= 1 { mid1[q + 1] } else { mid[q + 1] } };
                    rows[g].push((pk, k as u8, nx));
                }
            }
        }
    }
    for (s, row) in rows.iter().enumerate() {
        let tot: f64 = row.iter().map(|x| x.0).sum();
        let want = if s < 2 { 1.0 - tb.eps } else { 1.0 };
        assert!((tot - want).abs() < 1e-12, "row {} sums to {}", names[s], tot);
    }
    Chain { nst, rows, tid }
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let tb = read_tab(&a[1]);
    let tiny: f64 = a.get(2).map(|x| x.parse().unwrap()).unwrap_or(1e-12);
    let ch = build(&tb);
    let (j, t, pmax, eps, rho) = (tb.j, tb.t, tb.tp, tb.eps, tb.rho);
    assert!(j <= 5 && t <= 15 && pmax <= 127);
    println!("table {} J {} T {} T' {}; child states {} (with {} max-chain states)", a[1], j, t, pmax, ch.nst, 3 * (j - 1));
    println!("threshold {:e}", tiny);
    let mut start: Map<u64, f64> = Map::default();
    start.insert(enc(&[0; D], 0, 0, &[0; 6]), 1.0);
    let mut tot_exp = 0u64;
    let mut tot_con = 0u64;
    let mut tot_dist = 0u64;
    for i in 1..=j {
        let mut groups: Map<u64, Vec<(u64, f64)>> = Map::default();
        for (k, m) in start.drain() {
            let (c, e, _, o) = dec(k);
            groups.entry(k & 0xFFFFF).or_default().push((enc(&c, e, 1, &o), m));
        }
        let ngroups = groups.len();
        let mut newstart: Map<u64, f64> = Map::default();
        let (mut pe, mut pc, mut pd, mut rounds_max) = (0u64, 0u64, 0u64, 0usize);
        let mut chp: Set = Set::default();
        let mut chonly: Set = Set::default();
        let mut occ: Map<u64, f64> = Map::default();
        for (_, g) in groups.drain() {
            let mut pend: Map<u64, f64> = Map::default();
            for (k, m) in g {
                *pend.entry(k).or_insert(0.0) += m;
            }
            let mut seen: Set = Set::default();
            let mut fin: Map<u64, f64> = Map::default();
            let mut rounds = 0;
            while !pend.is_empty() {
                rounds += 1;
                let mut next: Map<u64, f64> = Map::with_capacity_and_hasher(pend.len(), Default::default());
                for (k, m) in pend.drain() {
                    let (c, e, p, o) = dec(k);
                    if m < tiny {
                        continue;
                    }
                    pe += 1;
                    if seen.insert(k) {
                        pd += 1;
                    }
                    let kc = (k >> 32) << 7 | p as u64;
                    chp.insert(kc);
                    chonly.insert(k >> 32);
                    *occ.entry(kc).or_insert(0.0) += m;
                    let w = m / (D as f64 + 1.0);
                    pc += 1;
                    if e as usize + 1 > t {
                    } else if p == 1 {
                        *fin.entry(enc(&c, e + 1, 0, &o)).or_insert(0.0) += w;
                    } else {
                        *next.entry(enc(&c, e + 1, p - 1, &o)).or_insert(0.0) += w;
                    }
                    for cc in 0..D {
                        if cc > 0 && c[cc] == c[cc - 1] {
                            continue;
                        }
                        let mult = c.iter().filter(|&&x| x == c[cc]).count() as f64;
                        let cs = c[cc] as usize;
                        let push = |nx: u16, dl: usize, mass: f64, next: &mut Map<u64, f64>, fin: &mut Map<u64, f64>| {
                            let np = p as usize - 1 + dl;
                            let mut c2 = c;
                            c2[cc] = nx;
                            let c2 = sort4(c2);
                            if np > pmax {
                            } else if np == 0 {
                                *fin.entry(enc(&c2, e, 0, &o)).or_insert(0.0) += mass;
                            } else {
                                *next.entry(enc(&c2, e, np as u32, &o)).or_insert(0.0) += mass;
                            }
                        };
                        for &(pr, dl, nx) in &ch.rows[cs] {
                            pc += 1;
                            push(nx, dl as usize, w * pr * mult, &mut next, &mut fin);
                        }
                        if cs < 2 {
                            let q0 = if cs == 0 { 2 } else { 1 };
                            let nx = ch.tid[q0];
                            let base = w * eps * mult;
                            let tmax = (pmax + 1).saturating_sub(p as usize);
                            for tt in (t + 1)..=tmax.max(t) {
                                pc += 1;
                                let pr = (1.0 - rho) * rho.powi((tt - t - 1) as i32);
                                push(nx, tt, base * pr, &mut next, &mut fin);
                            }
                            pc += 1;
                        }
                    }
                }
                pend = next;
            }
            rounds_max = rounds_max.max(rounds);
            for (k, m) in fin.drain() {
                let (c, e, _, mut o) = dec(k);
                o[i - 1] = e as u8;
                *newstart.entry(enc(&c, e, 0, &o)).or_insert(0.0) += m;
            }
        }
        println!(
            "phase {}: prefix groups {}, longest sub-run {}, state expansions {}, contributions {}, distinct (multiset, e, p, prefix) {}, distinct (multiset, p) {}, distinct multisets {}, next starts {}",
            i, ngroups, rounds_max, pe, pc, pd, chp.len(), chonly.len(), newstart.len()
        );
        let mut rep = Vec::new();
        for tau in [1e-5, 1e-6, 1e-7, 1e-8, 1e-9, 1e-10] {
            rep.push(format!("{:.0e}:{}", tau, occ.values().filter(|x| **x >= tau).count()));
        }
        println!("  phase {} (multiset, p) by summed occupation, threshold:count at or above {:?}", i, rep);
        if let (Ok(path), Ok(tau)) = (std::env::var("XDP_HEAVY_OUT"), std::env::var("XDP_HEAVY_TAU")) {
            let tau: f64 = tau.parse().unwrap();
            let mut s = String::new();
            for (k, v) in &occ {
                if *v >= tau {
                    s.push_str(&format!("{} {} {:e}\n", i, k, v));
                }
            }
            let mut f = std::fs::OpenOptions::new().create(true).append(true).open(&path).unwrap();
            std::io::Write::write_all(&mut f, s.as_bytes()).unwrap();
        }
        tot_exp += pe;
        tot_con += pc;
        tot_dist += pd;
        start = newstart;
    }
    println!("total: state expansions {}, contributions {}, distinct states (summed over phases and groups) {}", tot_exp, tot_con, tot_dist);
}
