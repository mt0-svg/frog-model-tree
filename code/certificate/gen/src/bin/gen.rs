// Generator of the backward certificate of a lumped chain, code/certificate/FORMAT.md version 4.
// Usage: gen --table PATH --table-ref REL --occ OCC --hmin X --out DATA[.zst] --info INFO
//   PATH: the version 3 table; REL: the path written in the `table` line (relative to the data file);
//   OCC: occupations "phase key occupation" (occupations with XDP_HEAVY_OUT, child indices in the FORMAT order,
//   7 bits each, then 7 bits of p); the flag of a state is 1 if its (multiset, p) has occupation >= X.
// The floating-point part (Gauss-Seidel, Z, the plan's max flow) only builds candidates; the values
// written are on the 2^-40 grid, made sound by the eta Z and theta^b Z rules, and checked exactly
// (items 4 and 5) on the merged moves before writing.
use certificate::sha256::Sha256;
use certificate::*;
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::collections::{HashMap, HashSet};
use std::io::Write;

const ABS: u32 = u32::MAX;

#[derive(Clone, Copy)]
struct MM {
    tgt: u32,
    f: u8,
    lo: u64,
    hi: u64,
}

struct HashW<W: Write> {
    inner: W,
    sha: Sha256,
    n: u64,
}
impl<W: Write> Write for HashW<W> {
    fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
        self.inner.write_all(b)?;
        self.sha.update(b);
        self.n += b.len() as u64;
        Ok(b.len())
    }
    fn flush(&mut self) -> std::io::Result<()> {
        self.inner.flush()
    }
}

fn arg(a: &[String], k: &str) -> Option<String> {
    a.iter().position(|x| x == k).map(|i| a[i + 1].clone())
}

// a floating-point max flow (Dinic) from sup into rec along x <= y; returns the flow per edge
fn flow_f64(sup: &[(Vec<u32>, f64)], rec: &[(Vec<u32>, f64)]) -> (f64, Vec<(usize, usize, f64)>) {
    let (nx, ny) = (sup.len(), rec.len());
    let n = 2 + nx + ny;
    let mut to: Vec<usize> = Vec::new();
    let mut cp: Vec<f64> = Vec::new();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    let add = |a: usize, b: usize, c: f64, to: &mut Vec<usize>, cp: &mut Vec<f64>, adj: &mut Vec<Vec<usize>>| {
        adj[a].push(to.len());
        to.push(b);
        cp.push(c);
        adj[b].push(to.len());
        to.push(a);
        cp.push(0.0);
    };
    for (i, s) in sup.iter().enumerate() {
        add(0, 2 + i, s.1, &mut to, &mut cp, &mut adj);
    }
    for (k, r) in rec.iter().enumerate() {
        add(2 + nx + k, 1, r.1, &mut to, &mut cp, &mut adj);
    }
    let mut mid = Vec::new();
    for (i, (x, _)) in sup.iter().enumerate() {
        for (k, (y, _)) in rec.iter().enumerate() {
            if x.iter().zip(y.iter()).all(|(a, b)| a <= b) {
                mid.push((i, k, to.len()));
                add(2 + i, 2 + nx + k, 1e9, &mut to, &mut cp, &mut adj);
            }
        }
    }
    let tiny = 1e-30;
    let mut total = 0.0;
    loop {
        let mut level = vec![-1i32; n];
        level[0] = 0;
        let mut qu = std::collections::VecDeque::new();
        qu.push_back(0usize);
        while let Some(u) = qu.pop_front() {
            for &e in &adj[u] {
                if cp[e] > tiny && level[to[e]] < 0 {
                    level[to[e]] = level[u] + 1;
                    qu.push_back(to[e]);
                }
            }
        }
        if level[1] < 0 {
            break;
        }
        let mut it = vec![0usize; n];
        loop {
            let mut path: Vec<usize> = Vec::new();
            let mut u = 0usize;
            let found = loop {
                if u == 1 {
                    break true;
                }
                let mut adv = false;
                while it[u] < adj[u].len() {
                    let e = adj[u][it[u]];
                    if cp[e] > tiny && level[to[e]] == level[u] + 1 {
                        path.push(e);
                        u = to[e];
                        adv = true;
                        break;
                    }
                    it[u] += 1;
                }
                if !adv {
                    if u == 0 {
                        break false;
                    }
                    level[u] = -1;
                    let e = path.pop().unwrap();
                    u = to[e ^ 1];
                    it[u] += 1;
                }
            };
            if !found {
                break;
            }
            let b = path.iter().map(|&e| cp[e]).fold(f64::INFINITY, f64::min);
            for &e in &path {
                cp[e] -= b;
                cp[e ^ 1] += b;
            }
            total += b;
        }
    }
    let fl = mid.into_iter().map(|(i, k, e)| (i, k, cp[e ^ 1])).filter(|x| x.2 > 0.0).collect();
    (total, fl)
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let tpath = arg(&a, "--table").expect("--table");
    let tref = arg(&a, "--table-ref").expect("--table-ref");
    let occ = arg(&a, "--occ").expect("--occ");
    let hmin: f64 = arg(&a, "--hmin").expect("--hmin").parse().unwrap();
    let outp = arg(&a, "--out").expect("--out");
    let infop = arg(&a, "--info").expect("--info");
    let ttext = std::fs::read(&tpath).unwrap();
    let tsha = certificate::sha256::hex_of(&ttext);
    let tb = read_table(std::str::from_utf8(&ttext).unwrap()).unwrap();
    println!("table {} sha256 {}; J {} T {} T' {}; hmin {:e}", tpath, tsha, tb.j, tb.t, tb.tp, hmin);
    let tv = check_table(&tb);
    for l in &tv.lines {
        println!("{}", l);
    }
    let chain = build_chain(&tb);
    let theta_f = f(&chain.theta);
    println!("child states {}; theta = {} (~{:.10})", chain.names.len(), chain.theta, theta_f);
    for (i, n) in chain.names.iter().enumerate() {
        if n.ends_with(":M") {
            let row: Vec<String> = chain.rows[i].iter().map(|x| format!("{}:{:.5}", x.delta, f(&x.p))).collect();
            println!("  {} row {:?}, w {:.6}", n, row, f(&chain.w[i]));
        }
    }
    let ctx = Ctx::new(&tb, chain);
    let (j, t, tp) = (tb.j, tb.t, tb.tp);
    let cps = comps(j, t);
    let nch = ctx.nch;
    // heavy pairs
    let mut heavy: HashSet<u64> = HashSet::new();
    let mut hcount = vec![0usize; j + 1];
    for l in std::fs::read_to_string(&occ).unwrap().lines() {
        let w: Vec<&str> = l.split_whitespace().collect();
        let (q, k, o): (usize, u64, f64) = (w[0].parse().unwrap(), w[1].parse().unwrap(), w[2].parse().unwrap());
        if o < hmin {
            continue;
        }
        let p = (k & 127) as usize;
        let mut r = k >> 7;
        let mut s = [0u8; 4];
        for i in (0..4).rev() {
            s[i] = (r & 127) as u8;
            r >>= 7;
        }
        assert!(r == 0 && s.iter().all(|c| (*c as usize) < nch) && s.windows(2).all(|x| x[0] <= x[1]) && (1..=j).contains(&q) && p >= 1 && p <= tp, "bad occupation line {}", l);
        heavy.insert(key(q, &s, p));
        hcount[q] += 1;
    }
    println!("heavy pairs per phase {:?}", &hcount[1..]);
    let resolve = |q: usize, s: &[u8; 4], p: usize| -> u64 {
        let k = key(q, s, p);
        if heavy.contains(&k) {
            k
        } else {
            key(q, &ctx.lump(s), p)
        }
    };
    // the reachable set, phase by phase
    let mut cache: HashMap<[u8; 4], Fr> = HashMap::new();
    let mut mv: Vec<Move> = Vec::new();
    let s0 = key(1, &[0u8; 4], 1);
    let mut phases: Vec<Vec<u64>> = vec![Vec::new(); j + 1];
    let mut starts: Vec<u64> = vec![s0];
    for q in 1..=j {
        let mut seen: HashSet<u64> = HashSet::new();
        let mut list: Vec<u64> = Vec::new();
        starts.sort_unstable();
        starts.dedup();
        for k in starts.drain(..) {
            if seen.insert(k) {
                list.push(k);
            }
        }
        let mut nexts: HashSet<u64> = HashSet::new();
        let mut qi = 0;
        while qi < list.len() {
            let (_, s, p) = unkey(list[qi]);
            qi += 1;
            ctx.moves(q, &s, p, false, &mut cache, &mut mv);
            for m in mv.iter() {
                if let Out::Reach(qt, s2, p2) = m.out {
                    let k = resolve(qt, &s2, p2);
                    if qt == q {
                        if seen.insert(k) {
                            list.push(k);
                        }
                    } else {
                        nexts.insert(k);
                    }
                }
            }
        }
        starts = nexts.into_iter().collect();
        phases[q] = list;
    }
    let keys: Vec<u64> = (1..=j).flat_map(|q| phases[q].iter().copied()).collect();
    let n = keys.len();
    let gidx: HashMap<u64, u32> = keys.iter().enumerate().map(|(i, k)| (*k, i as u32)).collect();
    let phase_of: Vec<usize> = keys.iter().map(|k| unkey(*k).0).collect();
    let flag: Vec<bool> = keys.iter().map(|k| heavy.contains(k)).collect();
    println!(
        "R per phase {:?} (total {}); flagged {}; states with a labelled child {}",
        (1..=j).map(|q| phases[q].len()).collect::<Vec<_>>(),
        n,
        flag.iter().filter(|x| **x).count(),
        keys.iter().filter(|k| ctx.has_label(&unkey(**k).1)).count()
    );
    // merged moves and stops
    let mut mstart: Vec<usize> = Vec::with_capacity(n + 1);
    let mut mms: Vec<MM> = Vec::new();
    let mut e0: Vec<u128> = vec![0; n];
    let mut stp: Vec<u128> = vec![0; n]; // cf + pp
    let (mut nraw, mut nstops) = (0u64, 0u64);
    let mut targets_hit: Vec<bool> = vec![false; n];
    for (kk, &k) in keys.iter().enumerate() {
        let (q, s, p) = unkey(k);
        let st = ctx.moves(q, &s, p, true, &mut cache, &mut mv);
        e0[kk] = st.e0_hi;
        stp[kk] = st.pp_hi + st.cf_hi;
        nstops += st.n_stops as u64;
        mstart.push(mms.len());
        let mut loc: Vec<MM> = Vec::new();
        for m in mv.iter() {
            nraw += 1;
            let tgt = match m.out {
                Out::Stop => continue,
                Out::Abs => ABS,
                Out::Reach(qt, s2, p2) => {
                    let g = *gidx.get(&resolve(qt, &s2, p2)).expect("target outside R");
                    targets_hit[g as usize] = true;
                    g
                }
            };
            match loc.iter_mut().find(|x| x.tgt == tgt && x.f == m.f) {
                Some(x) => {
                    x.lo += m.lo;
                    x.hi += m.hi;
                }
                None => loc.push(MM { tgt, f: m.f, lo: m.lo, hi: m.hi }),
            }
        }
        mms.extend(loc);
    }
    mstart.push(mms.len());
    println!("moves: raw {} ({:.1} per state, stops p' > T' included), merged non-stop {} ({:.1} per state); stops {}; product cache {}", nraw, nraw as f64 / n as f64, mms.len(), mms.len() as f64 / n as f64, nstops, cache.len());
    // value layout
    let lq: Vec<usize> = (0..=j + 1).map(|q| if q >= 1 { cps.len[q] } else { 0 }).collect();
    let mut voff: Vec<usize> = Vec::with_capacity(n + 1);
    let mut acc = 0usize;
    for kk in 0..n {
        voff.push(acc);
        acc += lq[phase_of[kk]];
    }
    voff.push(acc);
    let nw = t + 1;
    println!("vector lengths {:?}; numbers in V and W {}", &lq[1..=j], acc + n * nw);
    let p48 = 2f64.powi(-48);
    let decp: Vec<Vec<(usize, usize)>> = (0..=j).map(|q| if q == 0 { vec![] } else { cps.dec[q].iter().enumerate().filter(|x| *x.1 != NONE).map(|(i, &d)| (i, d as usize)).collect() }).collect();
    let nxp: Vec<Vec<Vec<(usize, usize)>>> = (0..2)
        .map(|f| (0..=j).map(|q| if q == 0 || q == j { vec![] } else { cps.nx[f][q].iter().enumerate().filter(|x| *x.1 != NONE).map(|(i, &d)| (i, d as usize)).collect() }).collect())
        .collect();
    let mut v = vec![0f64; acc];
    let mut wv = vec![0f64; n * nw];
    let mut z = vec![0f64; n];
    // right sides at state kk from the current values
    let eval = |kk: usize, v: &[f64], wv: &[f64], z: &[f64], nv: &mut Vec<f64>, nwv: &mut Vec<f64>| -> f64 {
        let q = phase_of[kk];
        nv.clear();
        nv.resize(lq[q], 0.0);
        nwv.clear();
        nwv.resize(nw, 0.0);
        nwv[0] += e0[kk] as f64 * p48;
        let sv = stp[kk] as f64 * p48;
        for x in nwv.iter_mut() {
            *x += sv;
        }
        let mut nz = 1.0;
        for m in &mms[mstart[kk]..mstart[kk + 1]] {
            let (wl, wh) = (m.lo as f64 * p48, m.hi as f64 * p48);
            if m.tgt == ABS {
                nv[m.f as usize] += wl;
                continue;
            }
            let g = m.tgt as usize;
            let tq = phase_of[g];
            let src = &v[voff[g]..voff[g + 1]];
            if tq == q {
                if m.f == 0 {
                    for (y, s) in nv.iter_mut().zip(src.iter()) {
                        *y += wl * s;
                    }
                } else {
                    for &(i, d) in &decp[q] {
                        nv[i] += wl * src[d];
                    }
                }
            } else {
                for &(i, d) in &nxp[m.f as usize][q] {
                    nv[i] += wl * src[d];
                }
            }
            let ws = &wv[g * nw..(g + 1) * nw];
            if m.f == 0 {
                for b in 0..nw {
                    nwv[b] += wh * ws[b];
                }
                nz += wh * z[g];
            } else {
                for b in 1..nw {
                    nwv[b] += wh * ws[b - 1];
                }
                nz += wh / theta_f * z[g];
            }
        }
        nz
    };
    let mut nv: Vec<f64> = Vec::new();
    let mut nwv: Vec<f64> = Vec::new();
    for q in (1..=j).rev() {
        let mut ord: Vec<usize> = (0..n).filter(|kk| phase_of[*kk] == q).collect();
        ord.sort_by_key(|kk| (keys[*kk] & 127, keys[*kk]));
        let mut sweeps = 0;
        loop {
            sweeps += 1;
            let (mut dmax, mut dz) = (0f64, 0f64);
            for &kk in &ord {
                let nz = eval(kk, &v, &wv, &z, &mut nv, &mut nwv);
                for (y, a) in v[voff[kk]..voff[kk + 1]].iter_mut().zip(nv.iter()) {
                    dmax = dmax.max((a - *y).abs());
                    *y = *a;
                }
                for (y, a) in wv[kk * nw..(kk + 1) * nw].iter_mut().zip(nwv.iter()) {
                    dmax = dmax.max((a - *y).abs());
                    *y = *a;
                }
                dz = dz.max((nz - z[kk]).abs() / nz);
                z[kk] = nz;
            }
            if (dmax < 1e-16 && dz < 1e-15) || sweeps >= 5000 {
                println!("Gauss-Seidel phase {}: {} states, {} sweeps, last change below 1e-16: {}", q, ord.len(), sweeps, dmax < 1e-16 && dz < 1e-15);
                break;
            }
        }
    }
    // residuals in floating point
    let (mut rvneg, mut rwpos, mut zres) = (0f64, 0f64, f64::INFINITY);
    for kk in 0..n {
        let nz = eval(kk, &v, &wv, &z, &mut nv, &mut nwv);
        for (a, y) in nv.iter().zip(v[voff[kk]..voff[kk + 1]].iter()) {
            rvneg = rvneg.max(y - a);
        }
        for (a, y) in nwv.iter().zip(wv[kk * nw..(kk + 1) * nw].iter()) {
            rwpos = rwpos.max(a - y);
        }
        zres = zres.min(z[kk] - (nz - 1.0)); // Z - K Z, should be about 1
    }
    let zmax = z.iter().cloned().fold(0.0, f64::max);
    println!("float residuals: V - right side and right side - W at most 1e-15: {}; min (Z - KZ) at least 1 - 1e-12: {}; Z(s0) {:.2}, max Z {:.2}", rvneg <= 1e-15 && rwpos <= 1e-15, zres >= 1.0 - 1e-12, z[0], zmax);
    let s0i = gidx[&s0] as usize;
    assert_eq!(s0i, 0);
    let wsf = &wv[s0i * nw..(s0i + 1) * nw];
    let rhs_f = f(&(&tb.eps * qpow(&ctx.chain.theta, t + 1)));
    println!("float: |V(s0)| {:.6}, W(s0)[T] {:.4e}, ratio to eps theta^(T+1) {:.4}", v[voff[0]..voff[1]].iter().sum::<f64>(), wsf[t], wsf[t] / rhs_f);
    // grid values, then the exact check of items 4 and 5 on the merged moves
    let two40 = 2f64.powi(40);
    let mut eta = 2f64.powi(-39);
    let mut etaw = rwpos.max(0.0) + 2f64.powi(-40) * theta_f;
    let thpow: Vec<f64> = (0..nw).map(|b| theta_f.powi(b as i32)).collect();
    let mut vi: Vec<u64> = vec![0; acc];
    let mut wi: Vec<u64> = vec![0; n * nw];
    for round in 0..6 {
        for kk in 0..n {
            for i in voff[kk]..voff[kk + 1] {
                vi[i] = (two40 * (v[i] - eta * z[kk])).floor().max(0.0) as u64;
            }
            for b in 0..nw {
                let x = two40 * (wv[kk * nw + b] + etaw * thpow[b] * z[kk]);
                assert!(x < 2f64.powi(53));
                wi[kk * nw + b] = x.ceil() as u64;
            }
        }
        let (mut vbad, mut wbad) = (0usize, 0usize);
        let mut rv: Vec<u128> = Vec::new();
        for kk in 0..n {
            let q = phase_of[kk];
            rv.clear();
            rv.resize(lq[q], 0);
            let mut rw: Vec<u128> = vec![0; nw];
            rw[0] += e0[kk] << 40;
            for x in rw.iter_mut() {
                *x += stp[kk] << 40;
            }
            for m in &mms[mstart[kk]..mstart[kk + 1]] {
                let (lo, hi) = (m.lo as u128, m.hi as u128);
                if m.tgt == ABS {
                    rv[m.f as usize] += lo << 40;
                    continue;
                }
                let g = m.tgt as usize;
                let src = &vi[voff[g]..voff[g + 1]];
                if phase_of[g] == q {
                    if m.f == 0 {
                        for (y, s) in rv.iter_mut().zip(src.iter()) {
                            *y += lo * *s as u128;
                        }
                    } else {
                        for &(i, d) in &decp[q] {
                            rv[i] += lo * src[d] as u128;
                        }
                    }
                } else {
                    for &(i, d) in &nxp[m.f as usize][q] {
                        rv[i] += lo * src[d] as u128;
                    }
                }
                let ws = &wi[g * nw..(g + 1) * nw];
                if m.f == 0 {
                    for b in 0..nw {
                        rw[b] += hi * ws[b] as u128;
                    }
                } else {
                    for b in 1..nw {
                        rw[b] += hi * ws[b - 1] as u128;
                    }
                }
            }
            for (i, r) in rv.iter().enumerate() {
                if ((vi[voff[kk] + i] as u128) << 48) > *r {
                    vbad += 1;
                }
            }
            for b in 0..nw {
                if ((wi[kk * nw + b] as u128) << 48) < rw[b] {
                    wbad += 1;
                }
            }
        }
        println!("grid round {}: exact failures V {}, W {}", round, vbad, wbad);
        if vbad == 0 && wbad == 0 {
            break;
        }
        if vbad > 0 {
            eta *= 2.0;
        }
        if wbad > 0 {
            etaw *= 2.0;
        }
    }
    // L and the plan
    let ome = Q::one();
    let p40 = Q::new(BigInt::one(), BigInt::one() << 40usize);
    let mut sup: Vec<(Vec<u32>, Q)> = Vec::new();
    for (i, x) in cps.c[1].iter().enumerate() {
        let nn = vi[voff[0] + i];
        if nn > 0 {
            let mut b = Vec::new();
            let mut s = 0u32;
            for d in x {
                s += *d as u32;
                b.push(s);
            }
            sup.push((b, Q::from_integer(BigInt::from(nn)) * &p40));
        }
    }
    let rec = hstar(&tb);
    let lsum: Q = sup.iter().map(|x| x.1.clone()).fold(Q::zero(), |a, b| a + b);
    let hsum: Q = rec.iter().map(|x| x.1.clone()).fold(Q::zero(), |a, b| a + b);
    println!("L: {} atoms, |L| = {:.12}, |L| - sum h = {:.6e}; receivers {}", sup.len(), f(&lsum), f(&(&lsum - &hsum)), rec.len());
    let supf: Vec<(Vec<u32>, f64)> = sup.iter().map(|x| (x.0.clone(), f(&x.1) * (1.0 - 1e-12))).collect();
    let deficit = |d: f64| -> (f64, Vec<(usize, usize, f64)>) {
        let rf: Vec<(Vec<u32>, f64)> = rec.iter().map(|x| (x.0.clone(), f(&x.1) * (1.0 + d))).collect();
        let need: f64 = rf.iter().map(|x| x.1).sum();
        let (fl, e) = flow_f64(&supf, &rf);
        (need - fl, e)
    };
    let d0 = deficit(0.0).0;
    let mut delta = 0.0;
    if d0 < 1e-14 {
        let (mut lo, mut hi) = (0f64, 1e-3);
        for _ in 0..30 {
            let mid = 0.5 * (lo + hi);
            if deficit(mid).0 < 1e-14 {
                lo = mid;
            } else {
                hi = mid;
            }
        }
        delta = lo / 2.0;
        println!("float plan: deficit at delta 0 below 1e-14; plan built at delta {:.2e}", delta);
    } else {
        println!("float plan: deficit at delta 0 at least 1e-14; the plan of the partial flow is written");
    }
    let (_, edges) = deficit(delta);
    // exact amounts
    let mut amt: HashMap<(usize, usize), Q> = HashMap::new();
    let mut byrec: Vec<Vec<(usize, f64)>> = vec![Vec::new(); rec.len()];
    for &(i, k, fl) in &edges {
        byrec[k].push((i, fl));
    }
    let two60 = BigInt::one() << 60usize;
    let mut underfilled: Vec<usize> = Vec::new();
    for (k, es) in byrec.iter_mut().enumerate() {
        let h = &rec[k].1;
        let hf = f(h);
        let tot: f64 = es.iter().map(|x| x.1).sum();
        if hf > 0.0 && tot >= hf * (1.0 + delta / 2.0) && !es.is_empty() {
            es.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
            let mut rsum = Q::zero();
            for &(i, fl) in &es[1..] {
                let r = Q::new(BigInt::from(((fl / tot) * 2f64.powi(60)).floor() as u64), two60.clone());
                rsum += &r;
                amt.insert((i, k), h * r);
            }
            amt.insert((es[0].0, k), h * (&ome - rsum));
        } else {
            for &(i, fl) in es.iter() {
                // partial: the float amount, rounded down to 2^-80
                let r = Q::new(BigInt::from((fl * (1.0 - 1e-9) * 2f64.powi(80)).floor() as u128), BigInt::one() << 80usize);
                let r = if &r > h { h.clone() } else { r };
                amt.insert((i, k), r);
            }
            underfilled.push(k);
        }
    }
    let mut used: Vec<Q> = vec![Q::zero(); sup.len()];
    for ((i, _), x) in &amt {
        used[*i] += x;
    }
    let over = (0..sup.len()).filter(|i| used[*i] > sup[*i].1).count();
    println!("exact plan from the float flow: {} entries, {} receivers left to the exact greedy fill, {} sources overdrawn", amt.len(), underfilled.len(), over);
    for i in (0..sup.len()).filter(|i| used[*i] > sup[*i].1).take(5) {
        let fsum: f64 = edges.iter().filter(|e| e.0 == i).map(|e| e.2).sum();
        println!("  overdrawn source {:?}: L {:.17e}, used {:.17e}, float flow {:.17e}", sup[i].0, f(&sup[i].1), f(&used[i]), fsum);
    }
    assert_eq!(over, 0, "a source overdrawn by the rounded plan");
    // exact greedy fill of the remaining receivers from the undrawn source mass
    let mut unfilled = 0usize;
    let mut unf_mass = Q::zero();
    for &k in &underfilled {
        let (y, h) = (&rec[k].0, &rec[k].1);
        let mut have: Q = amt.iter().filter(|((_, kk), _)| *kk == k).map(|x| x.1.clone()).fold(Q::zero(), |a, b| a + b);
        let mut cands: Vec<usize> = (0..sup.len()).filter(|i| sup[*i].0.iter().zip(y.iter()).all(|(a, b)| a <= b)).collect();
        cands.sort_by(|a, b| (&sup[*b].1 - &used[*b]).cmp(&(&sup[*a].1 - &used[*a])));
        for i in cands {
            if &have >= h {
                break;
            }
            let room = &sup[i].1 - &used[i];
            if !room.is_positive() {
                continue;
            }
            let take = if room < h - &have { room } else { h - &have };
            used[i] += &take;
            have += &take;
            let e = amt.entry((i, k)).or_insert_with(Q::zero);
            *e = &*e + take;
        }
        if &have < h {
            unfilled += 1;
            unf_mass += h - have;
        }
    }
    println!("after the exact greedy fill: receivers not filled {}, missing mass {} (~{:.6e})", unfilled, if unfilled > 0 { unf_mass.to_string() } else { "0".into() }, f(&unf_mass));
    // the data file
    let mut child = None;
    let sink: Box<dyn Write> = if outp.ends_with(".zst") {
        let mut c = std::process::Command::new("zstd").args(["-q", "-f", "-T2", "-12", "-o", &outp]).stdin(std::process::Stdio::piped()).spawn().expect("zstd");
        let w = Box::new(c.stdin.take().unwrap());
        child = Some(c);
        w
    } else {
        Box::new(std::fs::File::create(&outp).unwrap())
    };
    let mut wr = HashW { inner: std::io::BufWriter::with_capacity(1 << 22, sink), sha: Sha256::new(), n: 0 };
    writeln!(wr, "version 4").unwrap();
    writeln!(wr, "# backward certificate of a lumped chain (FORMAT v4), cert4 impl1 generator; flags from occupations >= {:e}", hmin).unwrap();
    writeln!(wr, "table {}", tref).unwrap();
    writeln!(wr, "table_sha256 {}", tsha).unwrap();
    for kk in 0..n {
        let (q, s, p) = unkey(keys[kk]);
        writeln!(wr, "state {} {} {} {} {} {} {} {}", kk, q, p, flag[kk] as u8, ctx.chain.names[s[0] as usize], ctx.chain.names[s[1] as usize], ctx.chain.names[s[2] as usize], ctx.chain.names[s[3] as usize]).unwrap();
    }
    let mut line = String::new();
    for kk in 0..n {
        line.clear();
        line.push_str(&format!("V {}", kk));
        for x in &vi[voff[kk]..voff[kk + 1]] {
            line.push(' ');
            line.push_str(&x.to_string());
        }
        line.push('\n');
        wr.write_all(line.as_bytes()).unwrap();
        line.clear();
        line.push_str(&format!("W {}", kk));
        for x in &wi[kk * nw..(kk + 1) * nw] {
            line.push(' ');
            line.push_str(&x.to_string());
        }
        line.push('\n');
        wr.write_all(line.as_bytes()).unwrap();
    }
    let mut ents: Vec<(&(usize, usize), &Q)> = amt.iter().filter(|x| x.1.is_positive()).collect();
    ents.sort_by(|a, b| a.0.cmp(b.0));
    for ((i, k), x) in ents.iter() {
        let xs: Vec<String> = sup[*i].0.iter().map(|v| v.to_string()).collect();
        let ys: Vec<String> = rec[*k].0.iter().map(|v| v.to_string()).collect();
        writeln!(wr, "plan {} {} {}", xs.join(" "), ys.join(" "), x).unwrap();
    }
    wr.flush().unwrap();
    let nbytes = wr.n;
    let hex = wr.sha.hex();
    drop(wr.inner);
    if let Some(mut c) = child {
        let st = c.wait().unwrap();
        assert!(st.success(), "zstd failed");
    }
    println!("data: {} bytes uncompressed, sha256 of the uncompressed data {}; written to {}", nbytes, hex, outp);
    let info = format!(
        "states {}\ns0 0\ndata_bytes {}\ndata_sha256 {}\nplan_entries {}\n",
        n,
        nbytes,
        hex,
        ents.len()
    );
    std::fs::write(&infop, info).unwrap();
    let _ = BigInt::zero().to_u64();
}
