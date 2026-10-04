// d3-cert: outward-rounded evaluation and verification of the step map Phi of Definition 12.3 of the
// paper, of the seed of Section 13 and of the extension of Definition 12.4, for the certificate of
// Proposition 15.1 (2). The optional S4 terms (a second read of
// a child through the rows of the state) are not in the paper, and the certificate leaves them off.
//
// Every state value is a dyadic number n / 2^52 (cdf bounds F(k, g) and normalized deficit bounds
// delta(k), both in [0, 1]). Every bound is computed in binary64 with each operation moved one ulp
// outward (next_up for upper bounds, next_down for lower bounds), which bounds the exact value since
// round-to-nearest errs by at most half an ulp. Generation (seed, step, ext, tcheck) evaluates every
// term of the step map, stores the minimum rounded up to the grid together with the name of the
// term that attains it; verification (verify) recomputes the named term only and checks that the
// stored value is at least that term. Section 16.4 describes the certificate; the file format is
// that of write_cert and read_cert, and d_names and f_names list the names of the terms.

use std::env;
use std::fmt::Write as FmtWrite;
use std::fs;

const GRID: i32 = 52; // state values are n / 2^GRID
const W62: i32 = 62; // M1 masses are n / 2^62

// ---------------------------------------------------------------- directed rounding
#[inline]
fn up(x: f64) -> f64 {
    x.next_up()
}
#[inline]
fn dn(x: f64) -> f64 {
    x.next_down()
}
#[inline]
fn add_u(a: f64, b: f64) -> f64 {
    if a == 0.0 {
        b
    } else if b == 0.0 {
        a
    } else {
        up(a + b)
    }
}
#[inline]
fn add_d(a: f64, b: f64) -> f64 {
    if a == 0.0 {
        b
    } else if b == 0.0 {
        a
    } else {
        dn(a + b)
    }
}
#[inline]
fn mul_u(a: f64, b: f64) -> f64 {
    if a == 0.0 || b == 0.0 {
        0.0
    } else {
        up(a * b)
    }
}
#[inline]
fn mul_d(a: f64, b: f64) -> f64 {
    if a == 0.0 || b == 0.0 {
        0.0
    } else {
        dn(a * b).max(0.0)
    }
}
#[inline]
fn div_u(a: f64, b: f64) -> f64 {
    if a == 0.0 {
        0.0
    } else {
        up(a / b)
    }
}
#[inline]
fn div_d(a: f64, b: f64) -> f64 {
    if a == 0.0 {
        0.0
    } else {
        dn(a / b).max(0.0)
    }
}
#[inline]
fn sub_u(a: f64, b: f64) -> f64 {
    if b == 0.0 {
        a
    } else {
        up(a - b)
    }
}
// rational a / b rounded up and down (a, b < 2^53, so both are exact doubles)
fn rat_u(a: i64, b: i64) -> f64 {
    div_u(a as f64, b as f64)
}
fn rat_d(a: i64, b: i64) -> f64 {
    div_d(a as f64, b as f64)
}
// the grid: smallest n / 2^GRID >= x, as n (x in [0, 2])
fn grid_up(x: f64) -> u64 {
    assert!(x >= 0.0 && x <= 2.0, "grid_up out of range: {}", x);
    let s = x * (2f64).powi(GRID); // exact scaling
    s.ceil() as u64
}
fn from_grid(n: u64) -> f64 {
    n as f64 * (2f64).powi(-GRID) // exact for n < 2^53
}
const ONE: u64 = 1u64 << GRID;

// ---------------------------------------------------------------- tables
struct Tabs {
    cu: Vec<Vec<f64>>, // C(n, k) rounded up, Pascal's rule with upward additions
    cd: Vec<Vec<f64>>, // rounded down
    wq: Vec<Vec<f64>>, // C(n, M) 4^-n rounded up, w(n, M) = (w(n-1, M) + w(n-1, M-1)) / 4
}
impl Tabs {
    fn new(nc: usize, nw: usize) -> Tabs {
        let mut cu = vec![vec![0.0f64; nc + 1]; nc + 1];
        let mut cd = vec![vec![0.0f64; nc + 1]; nc + 1];
        for n in 0..=nc {
            cu[n][0] = 1.0;
            cd[n][0] = 1.0;
            for k in 1..=n {
                cu[n][k] = add_u(cu[n - 1][k - 1], cu[n - 1][k]);
                cd[n][k] = add_d(cd[n - 1][k - 1], cd[n - 1][k]);
            }
        }
        let mut wq = vec![vec![0.0f64; nw + 1]; nw + 1];
        wq[0][0] = 1.0;
        for n in 1..=nw {
            for m in 0..=n {
                let a = wq[n - 1][m];
                let b = if m > 0 { wq[n - 1][m - 1] } else { 0.0 };
                wq[n][m] = add_u(a, b) * 0.25; // exact division by 4 (no subnormals at these sizes)
            }
        }
        Tabs { cu, cd, wq }
    }
}

// P(Bin(n, a/b) <= v), rounded up (upr) or down, by the pmf recursion
fn bin_le(n: usize, a: i64, b: i64, v: i64, upr: bool) -> f64 {
    if v < 0 {
        return 0.0;
    }
    if v as usize >= n {
        return 1.0;
    }
    let (mul, div, add) = if upr {
        (mul_u as fn(f64, f64) -> f64, div_u as fn(f64, f64) -> f64, add_u as fn(f64, f64) -> f64)
    } else {
        (mul_d as fn(f64, f64) -> f64, div_d as fn(f64, f64) -> f64, add_d as fn(f64, f64) -> f64)
    };
    let qq = if upr { rat_u(b - a, b) } else { rat_d(b - a, b) };
    let mut pk = 1.0f64;
    for _ in 0..n {
        pk = mul(pk, qq);
    }
    let mut s = pk;
    for k in 0..(v as usize) {
        let num = ((n - k) as i64 * a) as f64;
        let den = ((k as i64 + 1) * (b - a)) as f64;
        pk = mul(pk, div(num, den));
        s = add(s, pk);
    }
    if upr {
        s.min(1.0)
    } else {
        s
    }
}
// P(Bin(n, 1/2) >= e) rounded up
fn bin_ge_half_u(n: usize, e: usize) -> f64 {
    if e > n {
        return 0.0;
    }
    let mut pk = (0.5f64).powi(n as i32); // exact
    let mut s = if e == 0 { pk } else { 0.0 };
    for k in 0..n {
        pk = mul_u(pk, div_u((n - k) as f64, (k + 1) as f64));
        if k + 1 >= e {
            s = add_u(s, pk);
        }
    }
    s.min(1.0)
}

// Lemma 11.1 (3) of the paper, second bound: (D + mu^(1/2)/2)/(mu - g - 1), D = delta mu,
// mu = (h + 1 + j)/3; 1 if mu <= g + 1
fn l12_u(delta: f64, h: i64, j: usize, g: usize) -> f64 {
    let num3 = h + 1 + j as i64;
    let den3 = num3 - 3 * (g as i64 + 1);
    if den3 <= 0 {
        return 1.0;
    }
    let mu_u = rat_u(num3, 3);
    let d_u = mul_u(delta, mu_u);
    let s_u = mul_u(up(mu_u.sqrt()), 0.5);
    let den = rat_d(den3, 3);
    div_u(add_u(d_u, s_u), den).min(1.0)
}
// exp(-x) <= 1 / sum_{n <= N} x^n / n!, the sum rounded down (x >= 0)
fn expneg_u(x_d: f64) -> f64 {
    let mut t = 1.0f64;
    let mut s = 1.0f64;
    for n in 1..2000 {
        t = div_d(mul_d(t, x_d), n as f64);
        s = add_d(s, t);
        if (n as f64) > x_d && t < s * 1e-18 {
            break;
        }
    }
    div_u(1.0, s)
}
// Lemma 11.1 (3) of the paper, third bound: D/((1 - t) mu - g) + exp(-t^2 mu/2), t = i/200,
// D = delta mu; 1 if (1 - t) mu <= g.
// The exponential depends on (h + 1 + j, i) only and is cached by the evaluator.
fn l12p_exp_u(h: i64, j: usize, i: usize) -> f64 {
    let num3 = h + 1 + j as i64;
    expneg_u(rat_d((i * i) as i64 * num3, 240000))
}
fn l12p_first_u(delta: f64, h: i64, j: usize, g: usize, i: usize) -> Option<f64> {
    let num3 = h + 1 + j as i64;
    let den600 = (200 - i as i64) * num3 - 600 * g as i64;
    if den600 <= 0 {
        return None;
    }
    let mu_u = rat_u(num3, 3);
    let d_u = mul_u(delta, mu_u);
    Some(div_u(d_u, rat_d(den600, 600)))
}
fn l12p_u(delta: f64, h: i64, j: usize, g: usize, i: usize) -> f64 {
    match l12p_first_u(delta, h, j, g, i) {
        None => 1.0,
        Some(a) => add_u(a, l12p_exp_u(h, j, i)).min(1.0),
    }
}

// ---------------------------------------------------------------- states and files
#[derive(Clone)]
struct St {
    h: i64,
    e: usize,
    gm: usize,
    f: Vec<Vec<u64>>, // [k][g], k = 0..=E (row 0 is ONE)
    d: Vec<u64>,      // [k], k = 0..=E (d[0] = ONE), normalized deficits
}
impl St {
    fn fv(&self, k: usize, g: usize) -> f64 {
        from_grid(self.f[k][g])
    }
    fn dv(&self, k: usize) -> f64 {
        from_grid(self.d[k])
    }
}
#[derive(Clone, Copy)]
struct Par {
    vm: usize,
    jm: usize,
    spine: bool,
    s4: bool,
    eb: usize,
    s4j: usize,
}
struct Cert {
    kind: String,
    lo: i64, // children heights [lo, hi] of the map (STEP: lo = hi = h - 1; CHECK: [a, b - 1]; SEED, EXT: lo = hi = h)
    hi: i64,
    par: Par,
    st: St,
    dn: Vec<String>,      // names of the deficits, [k]
    fnm: Vec<Vec<String>>, // names of the cdf values, [k][g]
    extra: Vec<String>,
}

fn write_cert(c: &Cert, path: &str) {
    let mut s = String::new();
    let p = &c.par;
    writeln!(s, "D3CERT 1").unwrap();
    writeln!(s, "kind {}", c.kind).unwrap();
    writeln!(s, "height {}", c.st.h).unwrap();
    writeln!(s, "children {} {}", c.lo, c.hi).unwrap();
    writeln!(s, "params {} {} {} {} {} {} {} {}", c.st.e, c.st.gm, p.vm, p.jm, p.spine as u8, p.s4 as u8, p.eb, p.s4j).unwrap();
    writeln!(s, "grid {}", GRID).unwrap();
    for x in c.extra.iter() {
        writeln!(s, "{}", x).unwrap();
    }
    for k in 1..=c.st.e {
        writeln!(s, "D {} {} {}", k, c.st.d[k], c.dn[k]).unwrap();
    }
    for k in 1..=c.st.e {
        write!(s, "F {}", k).unwrap();
        for g in 0..=c.st.gm {
            write!(s, " {}", c.st.f[k][g]).unwrap();
        }
        s.push('\n');
        write!(s, "N {}", k).unwrap();
        for g in 0..=c.st.gm {
            write!(s, " {}", c.fnm[k][g]).unwrap();
        }
        s.push('\n');
    }
    writeln!(s, "end").unwrap();
    fs::write(path, s).unwrap();
}

fn read_cert(path: &str) -> Cert {
    let txt = fs::read_to_string(path).unwrap_or_else(|_| panic!("cannot read {}", path));
    let mut kind = String::new();
    let (mut h, mut lo, mut hi) = (0i64, 0i64, 0i64);
    let mut e = 0usize;
    let mut gm = 0usize;
    let mut par = Par { vm: 0, jm: 0, spine: false, s4: false, eb: 0, s4j: 0 };
    let mut d: Vec<u64> = Vec::new();
    let mut f: Vec<Vec<u64>> = Vec::new();
    let mut dnm: Vec<String> = Vec::new();
    let mut fnm: Vec<Vec<String>> = Vec::new();
    let mut extra = Vec::new();
    let mut seen_end = false;
    for (ln, line) in txt.lines().enumerate() {
        let w: Vec<&str> = line.split_whitespace().collect();
        if w.is_empty() {
            continue;
        }
        match w[0] {
            "D3CERT" => assert!(ln == 0 && w[1] == "1", "{}: bad header", path),
            "kind" => kind = w[1].to_string(),
            "height" => h = w[1].parse().unwrap(),
            "children" => {
                lo = w[1].parse().unwrap();
                hi = w[2].parse().unwrap();
            }
            "params" => {
                e = w[1].parse().unwrap();
                gm = w[2].parse().unwrap();
                par = Par {
                    vm: w[3].parse().unwrap(),
                    jm: w[4].parse().unwrap(),
                    spine: w[5] == "1",
                    s4: w[6] == "1",
                    eb: w[7].parse().unwrap(),
                    s4j: w[8].parse().unwrap(),
                };
                d = vec![ONE; e + 1];
                f = vec![vec![ONE; gm + 1]; e + 1];
                dnm = vec![String::new(); e + 1];
                fnm = vec![vec![String::new(); gm + 1]; e + 1];
            }
            "grid" => assert!(w[1].parse::<i32>().unwrap() == GRID, "{}: grid {} not supported", path, w[1]),
            "D" => {
                let k: usize = w[1].parse().unwrap();
                d[k] = w[2].parse().unwrap();
                dnm[k] = w[3].to_string();
            }
            "F" => {
                let k: usize = w[1].parse().unwrap();
                assert!(w.len() == gm + 3, "{}: row F {} has {} values", path, k, w.len() - 2);
                for g in 0..=gm {
                    f[k][g] = w[2 + g].parse().unwrap();
                }
            }
            "N" => {
                let k: usize = w[1].parse().unwrap();
                assert!(w.len() == gm + 3, "{}: row N {} has {} names", path, k, w.len() - 2);
                for g in 0..=gm {
                    fnm[k][g] = w[2 + g].to_string();
                }
            }
            "end" => seen_end = true,
            _ => extra.push(line.to_string()),
        }
    }
    assert!(seen_end, "{}: no end line", path);
    Cert { kind, lo, hi, par, st: St { h, e, gm, f, d }, dn: dnm, fnm, extra }
}

// structural requirements on a state: values in [0, ONE], row 0 and d[0] equal to ONE, rows nondecreasing in g
fn check_shape(s: &St) -> Result<(), String> {
    if s.d[0] != ONE {
        return Err("d[0] != 1".into());
    }
    for k in 0..=s.e {
        if s.d[k] > ONE {
            return Err(format!("delta({}) > 1", k));
        }
        for g in 0..=s.gm {
            if s.f[k][g] > ONE {
                return Err(format!("F({}, {}) > 1", k, g));
            }
            if k == 0 && s.f[0][g] != ONE {
                return Err("row 0 != 1".into());
            }
            if g > 0 && s.f[k][g] < s.f[k][g - 1] {
                return Err(format!("row {} decreases at g = {}", k, g));
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------- the evaluator of Phi^up_[lo, hi]
// sizes: the grid G(q) of K and n0 of Definition 12.3 of the paper, as in d3-fhat
fn ngrid(q: usize, gm: usize) -> Vec<usize> {
    let mut v: Vec<usize> = [8, 16, 24, 32, 48, 64, 96, 128, 192, 256].iter().map(|x| q + x).filter(|&k| k <= q + gm + 1).collect();
    if v.last() != Some(&(q + gm + 1)) {
        v.push(q + gm + 1);
    }
    v
}

struct Ev<'a> {
    s: &'a St,
    par: Par,
    lo: i64,
    hi: i64,
    tabs: &'a Tabs,
    zb: Option<Vec<Vec<Vec<f64>>>>, // [J][M][s]
    s23: Option<(Vec<Vec<f64>>, Vec<Vec<f64>>)>,
    s4l: Option<(Vec<Vec<f64>>, Vec<Vec<f64>>)>,
    expc: std::collections::HashMap<(i64, usize, usize), f64>, // exp terms of Lemma 11.1 (3) of the paper by (h, j, i)
}

fn conv_u(a: &[f64], b: &[f64], len: usize) -> Vec<f64> {
    let mut h = vec![0.0f64; len];
    for (i, &x) in a.iter().enumerate().take(len) {
        if x == 0.0 {
            continue;
        }
        for (k, &y) in b[..len - i].iter().enumerate() {
            if y != 0.0 {
                h[i + k] = add_u(h[i + k], mul_u(x, y));
            }
        }
    }
    h
}

impl<'a> Ev<'a> {
    fn new(s: &'a St, par: Par, lo: i64, hi: i64, tabs: &'a Tabs) -> Ev<'a> {
        check_shape(s).unwrap_or_else(|e| panic!("input state at {}: {}", s.h, e));
        Ev { s, par, lo, hi, tabs, zb: None, s23: None, s4l: None, expc: Default::default() }
    }
    // exact pseudo-pmfs of the rows (grid values, nondecreasing rows)
    fn pmf(&self, k: usize) -> Vec<f64> {
        let s = self.s;
        (0..=s.gm).map(|g| if g == 0 { s.fv(k, 0) } else { s.fv(k, g) - s.fv(k, g - 1) }).collect()
    }
    fn ensure_zb(&mut self) {
        if self.zb.is_some() {
            return;
        }
        let (ee, len) = (self.s.e, self.s.gm + 1);
        let pm: Vec<Vec<f64>> = (0..=ee).map(|k| self.pmf(k)).collect();
        let cu = &self.tabs.cu;
        let mut z2 = vec![vec![0.0f64; len]; 2 * ee - 1];
        for (l, z2l) in z2.iter_mut().enumerate() {
            let lo = if l + 1 > ee { l + 1 - ee } else { 0 };
            for e2 in lo..=l.min(ee - 1) {
                let e3 = l - e2;
                if e2 > e3 {
                    break;
                }
                let w = if e2 == e3 { cu[l][e2] } else { mul_u(cu[l][e2], 2.0) };
                let h = conv_u(&pm[e2], &pm[e3], len);
                for s in 0..len {
                    z2l[s] = add_u(z2l[s], mul_u(w, h[s]));
                }
            }
        }
        let mmx = 3 * (ee - 1);
        let mut zb = vec![vec![vec![0.0f64; len]; mmx + 1]; ee + 1];
        for e1 in 0..ee {
            let mut cur = zb[e1].clone();
            for (mm, curm) in cur.iter_mut().enumerate().skip(e1) {
                let l = mm - e1;
                if l > 2 * ee - 2 {
                    continue;
                }
                let w = cu[mm][e1];
                let h = conv_u(&pm[e1], &z2[l], len);
                for s in 0..len {
                    curm[s] = add_u(curm[s], mul_u(w, h[s]));
                }
            }
            zb[e1 + 1] = cur;
        }
        self.zb = Some(zb);
    }
    // sum_M sum_s Psi_M(s) Z_M(s), rounded up
    fn query(&self, jz: usize, q: usize, vcut: Option<usize>, smax: usize) -> f64 {
        let z = &self.zb.as_ref().unwrap()[jz];
        let gm = self.s.gm;
        let wq = &self.tabs.wq;
        let mut tot = 0.0f64;
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
            let mut run = 0.0f64;
            for s in (0..=hi).rev() {
                if s >= lo {
                    run = run.max(wq[q + s][mm]);
                }
                tot = add_u(tot, mul_u(run, zm[s]));
            }
        }
        tot
    }
    // the bound (B) of Lemma 11.2 of the paper on the pseudo-laws (Lemma 11.3 (2)): P(e_1 < J) in the
    // j-closure, with K
    fn pb(&mut self, j: usize, jj: usize, kk: usize) -> f64 {
        let (ee, gm) = (self.s.e, self.s.gm);
        let q = j + 1;
        assert!(jj >= 1 && jj <= ee && kk > q && kk <= q + gm + 1, "bad (B) name j {} J {} K {}", j, jj, kk);
        self.ensure_zb();
        let smax = kk - q - 1;
        let t1 = self.query(jj, q, None, smax);
        let t2 = mul_u(mul_u(2.0, bin_ge_half_u(ee + jj - 1, ee)), self.s.fv(ee, smax));
        let t3 = bin_le(kk, 1, 4, jj as i64 - 1, true);
        add_u(add_u(t1, t2), t3).min(1.0)
    }
    // the bound (A) of Lemma 11.2 of the paper on the pseudo-laws (Lemma 11.3 (2)): P(X <= v) with n0
    fn ra(&mut self, j: usize, v: usize, n0: usize) -> f64 {
        let (ee, gm) = (self.s.e, self.s.gm);
        let q = j + 1;
        assert!(n0 > q && n0 <= q + gm + 1, "bad (A) name j {} v {} n0 {}", j, v, n0);
        self.ensure_zb();
        let smax = n0 - q - 1;
        let t1 = self.query(ee, q, Some(v), smax);
        let t2 = mul_u(mul_u(3.0, bin_ge_half_u(ee + v, ee)), self.s.fv(ee, smax));
        let t3 = bin_le(n0, 1, 4, v as i64, true);
        add_u(add_u(t1, t2), t3).min(1.0)
    }
    // worst-end ratio mu_h(kp) / mu_{h+1}(j) over h in {lo, hi}, rounded up
    fn ratio(&self, kp: usize, j: usize) -> f64 {
        [self.lo, self.hi].iter().map(|&h| rat_u(h + 1 + kp as i64, h + 2 + j as i64)).fold(0.0, f64::max)
    }
    fn ensure_s23(&mut self) {
        if self.s23.is_some() {
            return;
        }
        let (ee, gm) = (self.s.e, self.s.gm);
        let r = pseudo_law(&self.s.f[1], gm);
        let s2 = stage_laws_d(&r, &[(1, 4), (3, 11), (3, 10)], &[(1, 2), (3, 11), (0, 1)], &[(1, 4), (5, 11), (7, 10)], ee, ee + 1);
        let s3 = stage_laws_d(&r, &[(1, 4), (3, 11), (3, 10), (1, 3)], &[(3, 4), (6, 11), (3, 10), (0, 1)], &[(0, 1), (2, 11), (4, 10), (2, 3)], gm + 1, ee + 1);
        self.s23 = Some((s2, s3));
    }
    fn ensure_s4(&mut self) {
        if self.s4l.is_some() {
            return;
        }
        let p = self.par;
        self.s4l = Some(s4_laws_d(self.s, p.eb, p.s4j, self.tabs));
    }
    // E Dt_j(min(e, E)) <= Dt(E) + sum_{k < E} C(k) (Dt(k) - Dt(k + 1)), C(k) >= P(e <= k), Dt the
    // running minimum of delta(k') r(k', j) rounded up (tilde delta_j of Definition 12.3 of the paper)
    fn dt_term(&self, j: usize, law: &[f64]) -> f64 {
        let ee = self.s.e;
        let mut dt = vec![0.0f64; ee + 1];
        let mut run = f64::INFINITY;
        for k in 0..=ee {
            let dk = if k == 0 { 1.0 } else { self.s.dv(k) };
            run = run.min(mul_u(dk, self.ratio(k, j)));
            dt[k] = run;
        }
        let cdf = cdf_up(law, ee); // C(k) for k = 0..E-1
        let mut tot = dt[ee];
        for k in 0..ee {
            tot = add_u(tot, mul_u(cdf[k], sub_u(dt[k], dt[k + 1]).max(0.0)));
        }
        tot
    }
    // the deficit term named nm for row j; out: the output deficits already fixed (rows < j)
    fn d_term(&mut self, j: usize, nm: &str, out_d: &[u64]) -> f64 {
        let ee = self.s.e;
        if nm == "T" {
            return self.ratio(0, j);
        }
        if nm == "P" {
            assert!(j >= 2, "pointer P at j = 1");
            return from_grid(out_d[j - 1]);
        }
        if nm == "S2" {
            assert!(self.par.spine, "S2 named without the spine terms");
            self.ensure_s23();
            let law = self.s23.as_ref().unwrap().0[j + 1].clone();
            return self.dt_term(j, &law);
        }
        if nm == "S4" {
            assert!(self.par.s4 && j <= self.par.s4j, "S4 named outside the S4 terms");
            self.ensure_s4();
            let law = self.s4l.as_ref().unwrap().1[j + 1].clone();
            return self.dt_term(j, &law);
        }
        if let Some(rest) = nm.strip_prefix('L') {
            let w: Vec<usize> = rest.split('.').map(|x| x.parse().unwrap()).collect();
            let (jj, kk) = (w[0], w[1]);
            assert!(jj >= 1 && jj <= self.par.jm && jj <= ee, "L name with J {} outside 1..JM", jj);
            let p = self.pb(j, jj, kk);
            let dj = self.s.dv(jj);
            let inner = add_u(dj, mul_u(p, 1.0 - dj)); // 1 - dj exact on the grid
            return mul_u(inner, self.ratio(jj, j));
        }
        panic!("unknown deficit name {}", nm);
    }
    // the cdf term named nm at (j, g); out: the output state (deficits all fixed, cdf rows < j and
    // (j, g' > g) fixed); hp the lowest parent height
    fn f_term(&mut self, j: usize, g: usize, nm: &str, out: &St) -> f64 {
        let hp = self.lo + 1;
        match nm {
            "1" => 1.0,
            "C" => bin_le(j, 1, 3, g as i64, true),
            "L" => l12_u(out.dv(j), hp, j, g),
            "J" => {
                assert!(j >= 2, "pointer J at j = 1");
                out.fv(j - 1, g)
            }
            "G" => {
                assert!(g < out.gm, "pointer G at g = GM");
                out.fv(j, g + 1)
            }
            "S3" => {
                assert!(self.par.spine, "S3 named without the spine terms");
                self.ensure_s23();
                let law = &self.s23.as_ref().unwrap().1[j + 1];
                tail_up(law, g)
            }
            "S4" => {
                assert!(self.par.s4 && j <= self.par.s4j, "S4 named outside the S4 terms");
                self.ensure_s4();
                let law = &self.s4l.as_ref().unwrap().0[j + 1];
                tail_up(law, g)
            }
            _ => {
                if let Some(rest) = nm.strip_prefix('t') {
                    let i: usize = rest.parse().unwrap();
                    assert!((1..200).contains(&i), "t name {} outside 1..199", i);
                    return match l12p_first_u(out.dv(j), hp, j, g, i) {
                        None => 1.0,
                        Some(x) => {
                            let ex = *self.expc.entry((hp, j, i)).or_insert_with(|| l12p_exp_u(hp, j, i));
                            add_u(x, ex).min(1.0)
                        }
                    };
                }
                if let Some(rest) = nm.strip_prefix('A') {
                    let n0: usize = rest.parse().unwrap();
                    assert!(g <= self.par.vm, "A name at g {} > VM", g);
                    return self.ra(j, g, n0);
                }
                panic!("unknown cdf name {}", nm)
            }
        }
    }
}

// pseudo-law of a nondecreasing grid row: r[g] = F(g) - F(g - 1), r[GM + 1] = 1 - F(GM); exact
fn pseudo_law(row: &[u64], gm: usize) -> Vec<f64> {
    let mut r = vec![0.0f64; gm + 2];
    for g in 0..=gm {
        let prev = if g == 0 { 0 } else { row[g - 1] };
        r[g] = from_grid(row[g] - prev);
    }
    r[gm + 1] = from_grid(ONE - row[gm]);
    r
}
// P(X <= g) <= 1 - sum_{x > g} law(x), law rounded down
fn tail_up(law: &[f64], g: usize) -> f64 {
    let mut s = 0.0f64;
    for x in (g + 1)..law.len() {
        s = add_d(s, law[x]);
    }
    sub_u(1.0, s).clamp(0.0, 1.0)
}
// C(k) = tail_up at k for k = 0..len-2
fn cdf_up(law: &[f64], ee: usize) -> Vec<f64> {
    (0..ee).map(|k| tail_up(law, k)).collect()
}

// the laws a^(2) and a^(3) of Lemma 12.1 of the paper (the terms S2 and S3) with every mass rounded down:
// stage f, count probability pc, new child pn, gone pg
fn stage_laws_d(r: &[f64], pc: &[(i64, i64)], pn: &[(i64, i64)], pg: &[(i64, i64)], cap: usize, y0: usize) -> Vec<Vec<f64>> {
    let ns = pc.len();
    let rmax = r.len() - 1;
    let pcd: Vec<f64> = pc.iter().map(|&(a, b)| rat_d(a, b)).collect();
    let pnd: Vec<f64> = pn.iter().map(|&(a, b)| rat_d(a, b)).collect();
    let pgd: Vec<f64> = pg.iter().map(|&(a, b)| rat_d(a, b)).collect();
    let ylim = |f: usize| y0 + f * rmax;
    let fl = ns - 1;
    let mut nxt: Vec<Vec<f64>> = Vec::with_capacity(ylim(fl) + 1);
    let mut a0 = vec![0.0f64; cap + 1];
    a0[0] = 1.0;
    nxt.push(a0);
    for y in 1..=ylim(fl) {
        let mut a = vec![0.0f64; cap + 1];
        let prev = &nxt[y - 1];
        for k in 0..=cap {
            a[k] = add_d(a[k], mul_d(pgd[fl], prev[k]));
        }
        for k in 0..=cap {
            let t = (k + 1).min(cap);
            a[t] = add_d(a[t], mul_d(pcd[fl], prev[k]));
        }
        nxt.push(a);
    }
    for f in (0..fl).rev() {
        let mut cur: Vec<Vec<f64>> = Vec::with_capacity(ylim(f) + 1);
        let mut a0 = vec![0.0f64; cap + 1];
        a0[0] = 1.0;
        cur.push(a0);
        for y in 1..=ylim(f) {
            let mut a = vec![0.0f64; cap + 1];
            let prev = &cur[y - 1];
            for k in 0..=cap {
                a[k] = add_d(a[k], mul_d(pgd[f], prev[k]));
            }
            for k in 0..=cap {
                let t = (k + 1).min(cap);
                a[t] = add_d(a[t], mul_d(pcd[f], prev[k]));
            }
            for (rv, &rp) in r.iter().enumerate() {
                if rp == 0.0 {
                    continue;
                }
                let w = mul_d(pnd[f], rp);
                for (k, &x) in nxt[y - 1 + rv].iter().enumerate() {
                    a[k] = add_d(a[k], mul_d(w, x));
                }
            }
            cur.push(a);
        }
        nxt = cur;
    }
    nxt
}

// laws of the optional S4 terms (not in the paper) with every mass rounded down; returns
// (law of min(X*, GM + 1), law of min(e*_c, E)) for q = 2..=S4J + 1 (index q)
fn s4_laws_d(s: &St, eb: usize, jmax: usize, tabs: &Tabs) -> (Vec<Vec<f64>>, Vec<Vec<f64>>) {
    let (ee, gm) = (s.e, s.gm);
    assert!(eb >= 1 && eb <= ee && jmax <= ee);
    let cap = gm + 1;
    let l = cap + 1;
    let ymax = gm + 1;
    // pseudo-laws of F^(b, .) = min over k <= b of the rows (nondecreasing in g, exact differences)
    let mut py = vec![vec![0.0f64; ymax + 1]; eb + 1];
    let mut fr = vec![ONE; gm + 1];
    for b in 1..=eb {
        for g in 0..=gm {
            fr[g] = fr[g].min(s.f[b][g]);
        }
        py[b] = pseudo_law(&fr, gm);
    }
    let binrows = |a: i64, bden: i64, c: usize| -> Vec<Vec<f64>> {
        let (p, q) = (rat_d(a, bden), rat_d(bden - a, bden));
        let mut rows = Vec::with_capacity(ymax + 1);
        let mut r = vec![0.0f64; c + 1];
        r[0] = 1.0;
        rows.push(r.clone());
        for _ in 1..=ymax {
            let mut nx = vec![0.0f64; c + 1];
            for k in 0..=c {
                nx[k] = add_d(nx[k], mul_d(q, r[k]));
                let t = (k + 1).min(c);
                nx[t] = add_d(nx[t], mul_d(p, r[k]));
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
    let mix = |b: usize, rows: &[Vec<f64>]| -> Vec<f64> {
        let mut v = vec![0.0f64; rows[0].len()];
        for (y, &w) in py[b].iter().enumerate() {
            if w == 0.0 {
                continue;
            }
            for (x, &z) in rows[y].iter().enumerate() {
                v[x] = add_d(v[x], mul_d(w, z));
            }
        }
        v
    };
    let cd = &tabs.cd;
    let mult = |parts: &[usize]| -> f64 {
        let n: usize = parts.iter().sum();
        let mut c = 1.0f64;
        let mut rest = n;
        for &k in parts.iter().take(parts.len() - 1) {
            c = mul_d(c, cd[rest][k]);
            rest -= k;
        }
        c * (0.25f64).powi(n as i32) // exact scaling by a power of 2
    };
    let qmax = jmax + 1;
    let (c3, c4) = (rat_d(3, 10), rat_d(4, 10));
    let (a311, a211, a511) = (rat_d(3, 11), rat_d(2, 11), rat_d(5, 11));

    // three live children: the ups
    let b13 = binrows(1, 3, cap);
    let w3: Vec<Vec<f64>> = (0..=eb).map(|t| if t == 0 { unit(l) } else { mix(t, &b13) }).collect();
    let mut h2: Vec<Vec<Vec<f64>>> = vec![w3];
    for y in 1..=ymax {
        let p = &h2[y - 1];
        let cur: Vec<Vec<f64>> = (0..=eb)
            .map(|t| {
                let tp = (t + 1).min(eb);
                let mut v = vec![0.0f64; l];
                for x in 0..l {
                    let xu = (x + 1).min(cap);
                    v[xu] = add_d(v[xu], mul_d(c3, p[t][x]));
                    v[x] = add_d(v[x], add_d(mul_d(c3, p[tp][x]), mul_d(c4, p[t][x])));
                }
                v
            })
            .collect();
        h2.push(cur);
    }
    let mut w2: Vec<Vec<Vec<f64>>> = vec![Vec::new(); eb + 1];
    for bb in 1..=eb {
        w2[bb] = (0..=bb)
            .map(|t| {
                let rows: Vec<Vec<f64>> = (0..=ymax).map(|y| h2[y][t].clone()).collect();
                mix(bb, &rows)
            })
            .collect();
    }
    drop(h2);
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
    let mut w1: Vec<Vec<Vec<f64>>> = (0..=eb).map(|bb| (0..npair).map(|p| if need[bb][p] { vec![0.0f64; l] } else { Vec::new() }).collect()).collect();
    let mut pairs = Vec::with_capacity(npair);
    for s1 in 0..=eb {
        for s2 in 0..=s1 {
            pairs.push((s1, s2));
        }
    }
    let mut h1: Vec<Vec<f64>> = pairs.iter().map(|&(s1, s2)| if s1 == 0 { unit(l) } else { w2[s1][s2].clone() }).collect();
    for y in 0..=ymax {
        if y > 0 {
            let p = &h1;
            let cur: Vec<Vec<f64>> = pairs
                .iter()
                .map(|&(s1, s2)| {
                    let (i0, i1, i2) = (pid(s1, s2), pid((s1 + 1).min(eb), s2), pid(s1, (s2 + 1).min(eb)));
                    let mut v = vec![0.0f64; l];
                    for x in 0..l {
                        let xu = (x + 1).min(cap);
                        v[xu] = add_d(v[xu], mul_d(a311, p[i0][x]));
                        v[x] = add_d(v[x], add_d(mul_d(a311, add_d(p[i1][x], p[i2][x])), mul_d(a211, p[i0][x])));
                    }
                    v
                })
                .collect();
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
                        w1[bb][p][x] = add_d(w1[bb][p][x], mul_d(w, h1[p][x]));
                    }
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
                        let i = u0.min(cap);
                        v[i] = add_d(v[i], w);
                    } else {
                        for (x, &z) in w1[t[0]][pid(t[1], t[2])].iter().enumerate() {
                            let i = (x + u0).min(cap);
                            v[i] = add_d(v[i], mul_d(w, z));
                        }
                    }
                }
            }
        }
        lawx[q] = v;
    }

    // c dead, two live siblings: the entries into c
    let ce = ee;
    let b310 = binrows(3, 10, ce);
    let w2d: Vec<Vec<f64>> = (0..=eb).map(|t| if t == 0 { unit(ce + 1) } else { mix(t, &b310) }).collect();
    let mut h1d: Vec<Vec<Vec<f64>>> = vec![w2d];
    for y in 1..=ymax {
        let p = &h1d[y - 1];
        let cur: Vec<Vec<f64>> = (0..=eb)
            .map(|t| {
                let tp = (t + 1).min(eb);
                let mut v = vec![0.0f64; ce + 1];
                for x in 0..=ce {
                    let xu = (x + 1).min(ce);
                    v[xu] = add_d(v[xu], mul_d(a311, p[t][x]));
                    v[x] = add_d(v[x], add_d(mul_d(a311, p[tp][x]), mul_d(a511, p[t][x])));
                }
                v
            })
            .collect();
        h1d.push(cur);
    }
    let mut w1d: Vec<Vec<Vec<f64>>> = vec![Vec::new(); eb + 1];
    for bb in 1..=eb {
        w1d[bb] = (0..=bb)
            .map(|t| {
                let rows: Vec<Vec<f64>> = (0..=ymax).map(|y| h1d[y][t].clone()).collect();
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
                        let i = kc.min(ce);
                        v[i] = add_d(v[i], w);
                    } else {
                        for (x, &z) in w1d[hi][lo].iter().enumerate() {
                            let i = (x + kc).min(ce);
                            v[i] = add_d(v[i], mul_d(w, z));
                        }
                    }
                }
            }
        }
        lawe[q] = v;
    }
    (lawx, lawe)
}

// ---------------------------------------------------------------- generation
fn tabs_for(e: usize, gm: usize) -> Tabs {
    Tabs::new(3 * e + 2, e + 2 + gm + 1)
}
const INFL: f64 = 1.0 + 1.0 / 68719476736.0; // 1 + 2^-36: slack left for checkers with other arithmetic

fn store(x: f64) -> u64 {
    grid_up(mul_u(x, INFL).min(1.0))
}

// candidate names of the deficit row j
fn d_names(j: usize, par: &Par, e: usize, gm: usize) -> Vec<String> {
    let mut v = vec!["T".to_string()];
    if j >= 2 {
        v.push("P".into());
    }
    for jj in 1..=par.jm.min(e) {
        for kk in ngrid(j + 1, gm) {
            v.push(format!("L{}.{}", jj, kk));
        }
    }
    if par.spine {
        v.push("S2".into());
    }
    if par.s4 && j <= par.s4j {
        v.push("S4".into());
    }
    v
}
fn f_names(j: usize, g: usize, par: &Par, gm: usize) -> Vec<String> {
    let mut v = vec!["1".to_string()];
    if g < gm {
        v.push("G".into());
    }
    if j >= 2 {
        v.push("J".into());
    }
    v.push("C".into());
    v.push("L".into());
    for i in 1..200 {
        v.push(format!("t{}", i));
    }
    if g <= par.vm {
        for n0 in ngrid(j + 1, gm) {
            v.push(format!("A{}", n0));
        }
    }
    if par.spine {
        v.push("S3".into());
    }
    if par.s4 && j <= par.s4j {
        v.push("S4".into());
    }
    v
}

// one evaluation of Phi^up_[lo, hi] from s; target: None (generate a new state, height hi + 1) or Some(T)
// (name the terms below T, the interval check); returns the certificate and the largest term/stored ratio
fn eval_map(s: &St, par: Par, lo: i64, hi: i64, kind: &str, target: Option<&St>, nth: usize) -> (Cert, f64) {
    let (e, gm) = (s.e, s.gm);
    let tabs = tabs_for(e, gm);
    let mut ev = Ev::new(s, par, lo, hi, &tabs);
    let mut out = St { h: hi + 1, e, gm, f: vec![vec![ONE; gm + 1]; e + 1], d: vec![ONE; e + 1] };
    if let Some(t) = target {
        assert!(t.e == e && t.gm == gm);
        out = t.clone();
    }
    // the state the pointer terms (P, J, G) and the terms of Lemma 11.1 (3) of the paper read: in a
    // generation the stored new state; in the interval check the values of the named terms rounded up to
    // the grid (each a valid bound at the parent heights by induction over the components in this
    // order), not T itself
    let mut ptr = out.clone();
    let mut dnm = vec![String::new(); e + 1];
    let mut fnm = vec![vec![String::new(); gm + 1]; e + 1];
    let mut worst = 0.0f64;
    ev.ensure_zb();
    if par.spine {
        ev.ensure_s23();
    }
    if par.s4 {
        ev.ensure_s4();
    }
    // the (B) and (A) bounds for every name, in parallel over j (pure functions of the tables)
    let pbt: Vec<Vec<Vec<f64>>>;
    let rat: Vec<Vec<Vec<f64>>>;
    {
        let evr = &ev;
        let res: Vec<(usize, Vec<Vec<f64>>, Vec<Vec<f64>>)> = std::thread::scope(|sc| {
            let hs: Vec<_> = (0..nth)
                .map(|i| {
                    sc.spawn(move || {
                        let mut o = Vec::new();
                        for j in (1..=e).filter(|j| j % nth == i) {
                            let q = j + 1;
                            let gr = ngrid(q, gm);
                            let b: Vec<Vec<f64>> = (0..=par.jm.min(e))
                                .map(|jj| if jj == 0 { Vec::new() } else { gr.iter().map(|&kk| pb_pure(evr, j, jj, kk)).collect() })
                                .collect();
                            let a: Vec<Vec<f64>> = (0..=par.vm.min(gm)).map(|v| gr.iter().map(|&n0| ra_pure(evr, j, v, n0)).collect()).collect();
                            o.push((j, b, a));
                        }
                        o
                    })
                })
                .collect();
            hs.into_iter().flat_map(|h| h.join().unwrap()).collect()
        });
        let mut pb = vec![Vec::new(); e + 1];
        let mut ra = vec![Vec::new(); e + 1];
        for (j, b, a) in res {
            pb[j] = b;
            ra[j] = a;
        }
        pbt = pb;
        rat = ra;
    }
    let term_d = |ev: &mut Ev, j: usize, nm: &str, od: &[u64]| -> f64 {
        if let Some(rest) = nm.strip_prefix('L') {
            let w: Vec<usize> = rest.split('.').map(|x| x.parse().unwrap()).collect();
            let gi = ngrid(j + 1, gm).iter().position(|&k| k == w[1]).unwrap();
            let p = pbt[j][w[0]][gi];
            let dj = ev.s.dv(w[0]);
            return mul_u(add_u(dj, mul_u(p, 1.0 - dj)), ev.ratio(w[0], j));
        }
        ev.d_term(j, nm, od)
    };
    for j in 1..=e {
        let mut best = (f64::INFINITY, String::new());
        for nm in d_names(j, &par, e, gm) {
            let v = term_d(&mut ev, j, &nm, &ptr.d);
            if v < best.0 {
                best = (v, nm);
            }
        }
        if target.is_none() {
            out.d[j] = store(best.0).min(ONE);
            ptr.d[j] = out.d[j];
        } else if from_grid(out.d[j]) < best.0 {
            panic!("interval check: delta_T({}) = {:e} below every term (best {} = {:e})", j, from_grid(out.d[j]), best.1, best.0);
        } else {
            ptr.d[j] = grid_up(best.0);
        }
        worst = worst.max(best.0 / from_grid(out.d[j]).max(1e-300));
        dnm[j] = best.1;
    }
    for j in 1..=e {
        for g in (0..=gm).rev() {
            let mut best = (f64::INFINITY, String::new());
            for nm in f_names(j, g, &par, gm) {
                let v = if let Some(rest) = nm.strip_prefix('A') {
                    let n0: usize = rest.parse().unwrap();
                    let gi = ngrid(j + 1, gm).iter().position(|&k| k == n0).unwrap();
                    rat[j][g][gi]
                } else {
                    ev.f_term(j, g, &nm, &ptr)
                };
                if v < best.0 {
                    best = (v, nm);
                }
            }
            if target.is_none() {
                // stored >= the named term; kept nondecreasing in g (the term G is a candidate, so the
                // minimum with F(j, g + 1) stays above the named term)
                let mut v = store(best.0).min(ONE);
                if g < gm {
                    v = v.min(out.f[j][g + 1]);
                }
                out.f[j][g] = v;
                ptr.f[j][g] = v;
            } else if from_grid(out.f[j][g]) < best.0 {
                panic!("interval check: F_T({}, {}) = {:e} below every term (best {} = {:e})", j, g, from_grid(out.f[j][g]), best.1, best.0);
            } else {
                ptr.f[j][g] = grid_up(best.0);
            }
            if out.f[j][g] < ONE {
                worst = worst.max(best.0 / from_grid(out.f[j][g]).max(1e-300));
            }
            fnm[j][g] = best.1;
        }
    }
    (Cert { kind: kind.to_string(), lo, hi, par, st: out, dn: dnm, fnm, extra: Vec::new() }, worst)
}
// thread-safe versions of pb and ra (the tables are built before the threads start)
fn pb_pure(ev: &Ev, j: usize, jj: usize, kk: usize) -> f64 {
    let (ee, gm) = (ev.s.e, ev.s.gm);
    let q = j + 1;
    assert!(kk > q && kk <= q + gm + 1);
    let smax = kk - q - 1;
    let t1 = ev.query(jj, q, None, smax);
    let t2 = mul_u(mul_u(2.0, bin_ge_half_u(ee + jj - 1, ee)), ev.s.fv(ee, smax));
    let t3 = bin_le(kk, 1, 4, jj as i64 - 1, true);
    add_u(add_u(t1, t2), t3).min(1.0)
}
fn ra_pure(ev: &Ev, j: usize, v: usize, n0: usize) -> f64 {
    let (ee, gm) = (ev.s.e, ev.s.gm);
    let q = j + 1;
    assert!(n0 > q && n0 <= q + gm + 1);
    let smax = n0 - q - 1;
    let t1 = ev.query(ee, q, Some(v), smax);
    let t2 = mul_u(mul_u(3.0, bin_ge_half_u(ee + v, ee)), ev.s.fv(ee, smax));
    let t3 = bin_le(n0, 1, 4, v as i64, true);
    add_u(add_u(t1, t2), t3).min(1.0)
}

// ---------------------------------------------------------------- seed, extension, hand-over
struct Masses {
    v: usize,             // the largest count (the saturated bin)
    n: Vec<Vec<u128>>,    // [k][x], x = 0..=v, natural numbers over 2^62
}
fn read_masses(path: &str, m0: i64, e: usize) -> Masses {
    let txt = fs::read_to_string(path).unwrap();
    let mut v = 0usize;
    let mut n: Vec<Vec<u128>> = vec![Vec::new(); e + 1];
    for line in txt.lines() {
        let w: Vec<&str> = line.split_whitespace().collect();
        if w.len() == 3 && w[0] == "MASSV" {
            assert!(w[1].parse::<i64>().unwrap() == m0, "masses file for another height");
            v = w[2].parse().unwrap();
            for k in 0..=e {
                n[k] = vec![0u128; v + 1];
            }
        }
        if w.len() == 5 && w[0] == "MASS" && w[1].parse::<i64>().ok() == Some(m0) {
            let k: usize = w[2].parse().unwrap();
            let x: usize = w[3].parse().unwrap();
            if k <= e {
                n[k][x] = w[4].parse().unwrap();
            }
        }
    }
    assert!(v > 0, "no MASSV line");
    for k in 1..=e {
        let tot: u128 = n[k].iter().sum();
        assert!(tot <= 1u128 << W62, "masses of k = {} sum above 1", k);
    }
    Masses { v, n }
}
// e_k rounded down and c_k(g) = 1 - sum_{x > g} mass rounded up (the mass missing below 2^62 sits at 0)
fn seed_mean_d(m: &Masses, k: usize) -> f64 {
    let s: u128 = m.n[k].iter().enumerate().map(|(x, &c)| x as u128 * c).sum();
    let f = s as f64; // round to nearest, then one step down
    let fd = if (f as u128) > s { dn(f) } else { f };
    fd * (2f64).powi(-W62)
}
fn seed_row_u(m: &Masses, k: usize, g: usize) -> f64 {
    let s: u128 = m.n[k].iter().skip(g + 1).sum();
    let r = (1u128 << W62) - s;
    let f = r as f64;
    let fu = if (f as u128) < r { up(f) } else { f };
    (fu * (2f64).powi(-W62)).min(1.0)
}
fn seed_d_term(m: &Masses, m0: i64, k: usize, nm: &str) -> f64 {
    if nm == "T" {
        return 1.0;
    }
    let kp: usize = nm.strip_prefix('M').expect("seed deficit name").parse().unwrap();
    assert!(kp >= 1 && kp <= k);
    let mu_kp = rat_u(m0 + 1 + kp as i64, 3);
    let mu_k = rat_d(m0 + 1 + k as i64, 3);
    div_u(sub_u(mu_kp, seed_mean_d(m, kp)).max(0.0), mu_k).min(1.0)
}
// cdf terms shared by the seed and the extension at a single height h (no step)
fn single_f_term(out: &St, h: i64, j: usize, g: usize, nm: &str, m: Option<&Masses>, inp: Option<&St>) -> f64 {
    match nm {
        "1" => 1.0,
        "C" => bin_le(j, 1, 3, g as i64, true),
        "L" => l12_u(out.dv(j), h, j, g),
        "J" => {
            assert!(j >= 2);
            out.fv(j - 1, g)
        }
        "G" => {
            assert!(g < out.gm);
            out.fv(j, g + 1)
        }
        "R" => {
            let m = m.expect("R outside the seed");
            assert!(g < m.v, "R at g >= V");
            seed_row_u(m, j, g)
        }
        "=" => {
            let s = inp.expect("= outside the extension");
            assert!(j <= s.e && g <= s.gm);
            s.fv(j, g)
        }
        _ => {
            let i: usize = nm.strip_prefix('t').unwrap_or_else(|| panic!("unknown name {}", nm)).parse().unwrap();
            assert!((1..200).contains(&i));
            l12p_u(out.dv(j), h, j, g, i)
        }
    }
}
fn single_names(j: usize, g: usize, gm: usize, extra: &[&str]) -> Vec<String> {
    let mut v = vec!["1".to_string()];
    if g < gm {
        v.push("G".into());
    }
    if j >= 2 {
        v.push("J".into());
    }
    v.push("C".into());
    v.push("L".into());
    for i in 1..200 {
        v.push(format!("t{}", i));
    }
    for x in extra {
        v.push(x.to_string());
    }
    v
}
fn gen_seed(m: &Masses, m0: i64, e: usize, gm: usize) -> Cert {
    let mut out = St { h: m0, e, gm, f: vec![vec![ONE; gm + 1]; e + 1], d: vec![ONE; e + 1] };
    let mut dnm = vec![String::new(); e + 1];
    let mut fnm = vec![vec![String::new(); gm + 1]; e + 1];
    for k in 1..=e {
        let mut best = (1.0f64, "T".to_string());
        for kp in 1..=k {
            let nm = format!("M{}", kp);
            let v = seed_d_term(m, m0, k, &nm);
            if v < best.0 {
                best = (v, nm);
            }
        }
        out.d[k] = store(best.0).min(ONE);
        dnm[k] = best.1;
    }
    for j in 1..=e {
        for g in (0..=gm).rev() {
            let ex: Vec<&str> = if g < m.v { vec!["R"] } else { vec![] };
            let mut best = (f64::INFINITY, String::new());
            for nm in single_names(j, g, gm, &ex) {
                let v = single_f_term(&out, m0, j, g, &nm, Some(m), None);
                if v < best.0 {
                    best = (v, nm);
                }
            }
            let mut v = store(best.0).min(ONE);
            if g < gm {
                v = v.min(out.f[j][g + 1]);
            }
            out.f[j][g] = v;
            fnm[j][g] = best.1;
        }
    }
    let par = Par { vm: 0, jm: 0, spine: false, s4: false, eb: 0, s4j: 0 };
    Cert { kind: "SEED".into(), lo: m0, hi: m0, par, st: out, dn: dnm, fnm, extra: Vec::new() }
}
// extension to (E2, GM2) at the same height (Definition 12.4 of the paper): D(k) <= D(E) for k > E,
// rows from F(E, .), coin and Lemma 11.1 (3)
fn ext_d_term(inp: &St, k: usize, nm: &str) -> f64 {
    match nm {
        "=" => {
            assert!(k <= inp.e);
            inp.dv(k)
        }
        "X" => {
            let (h, e) = (inp.h, inp.e);
            assert!(k > e);
            div_u(mul_u(inp.dv(e), rat_u(h + 1 + e as i64, 3)), rat_d(h + 1 + k as i64, 3)).min(1.0)
        }
        "T" => 1.0,
        _ => panic!("unknown extension deficit name {}", nm),
    }
}
fn gen_ext(inp: &St, e2: usize, gm2: usize) -> Cert {
    assert!(e2 >= inp.e && gm2 >= inp.gm);
    let h = inp.h;
    let mut out = St { h, e: e2, gm: gm2, f: vec![vec![ONE; gm2 + 1]; e2 + 1], d: vec![ONE; e2 + 1] };
    let mut dnm = vec![String::new(); e2 + 1];
    let mut fnm = vec![vec![String::new(); gm2 + 1]; e2 + 1];
    for k in 1..=e2 {
        let nm = if k <= inp.e { "=" } else { "X" };
        out.d[k] = if k <= inp.e { inp.d[k] } else { store(ext_d_term(inp, k, nm)).min(ONE) };
        dnm[k] = nm.to_string();
    }
    for j in 1..=e2 {
        for g in (0..=gm2).rev() {
            let ex: Vec<&str> = if j <= inp.e && g <= inp.gm { vec!["="] } else { vec![] };
            let mut best = (f64::INFINITY, String::new());
            for nm in single_names(j, g, gm2, &ex) {
                let v = single_f_term(&out, h, j, g, &nm, None, Some(inp));
                if v < best.0 {
                    best = (v, nm);
                }
            }
            let mut v = if best.1 == "=" { inp.f[j][g] } else { store(best.0).min(ONE) };
            if g < gm2 {
                v = v.min(out.f[j][g + 1]);
            }
            out.f[j][g] = v;
            fnm[j][g] = best.1;
        }
    }
    let par = Par { vm: 0, jm: 0, spine: false, s4: false, eb: 0, s4j: 0 };
    Cert { kind: "EXT".into(), lo: h, hi: h, par, st: out, dn: dnm, fnm, extra: Vec::new() }
}

// ---------------------------------------------------------------- verification
struct Report {
    worst: f64,
    counts: std::collections::BTreeMap<String, usize>,
}
fn count_name(r: &mut Report, nm: &str) {
    let key: String = if nm.starts_with('S') || nm == "1" || nm == "=" { nm.to_string() } else { nm.chars().take_while(|c| !c.is_ascii_digit()).collect() };
    *r.counts.entry(key).or_insert(0) += 1;
}
fn verify_step(c: &Cert, inp: &St) -> Result<Report, String> {
    let (e, gm) = (c.st.e, c.st.gm);
    check_shape(&c.st)?;
    if inp.e != e || inp.gm != gm {
        return Err("parameters differ from the input state".into());
    }
    let (lo, hi) = (c.lo, c.hi);
    if c.kind == "STEP" && !(lo == inp.h && hi == inp.h && c.st.h == inp.h + 1) {
        return Err(format!("STEP heights: input {} children [{}, {}] output {}", inp.h, lo, hi, c.st.h));
    }
    let tabs = tabs_for(e, gm);
    let mut ev = Ev::new(inp, c.par, lo, hi, &tabs);
    let mut rep = Report { worst: 0.0, counts: Default::default() };
    // the pointer terms and the terms of Lemma 11.1 (3) of the paper read the stored state in a STEP, the
    // named term values rounded up to the grid in a CHECK (as eval_map)
    let check = c.kind == "CHECK";
    let mut ptr = c.st.clone();
    for j in 1..=e {
        let t = ev.d_term(j, &c.dn[j], &ptr.d);
        let s = c.st.dv(j);
        if !(t <= s) {
            return Err(format!("delta({}) = {:e} < term {} = {:e}", j, s, c.dn[j], t));
        }
        if check {
            ptr.d[j] = grid_up(t);
        }
        rep.worst = rep.worst.max(t / s.max(1e-300));
        count_name(&mut rep, &c.dn[j]);
    }
    for j in 1..=e {
        for g in (0..=gm).rev() {
            let nm = &c.fnm[j][g];
            let t = ev.f_term(j, g, nm, &ptr);
            let s = c.st.fv(j, g);
            if !(t <= s) {
                return Err(format!("F({}, {}) = {:e} < term {} = {:e}", j, g, s, nm, t));
            }
            if check {
                ptr.f[j][g] = grid_up(t);
            }
            if c.st.f[j][g] < ONE {
                rep.worst = rep.worst.max(t / s.max(1e-300));
            }
            count_name(&mut rep, nm);
        }
    }
    Ok(rep)
}
fn verify_single(c: &Cert, m: Option<&Masses>, inp: Option<&St>) -> Result<Report, String> {
    let (e, gm, h) = (c.st.e, c.st.gm, c.st.h);
    check_shape(&c.st)?;
    let mut rep = Report { worst: 0.0, counts: Default::default() };
    for k in 1..=e {
        let nm = &c.dn[k];
        let t = if let Some(m) = m { seed_d_term(m, h, k, nm) } else { ext_d_term(inp.unwrap(), k, nm) };
        let s = c.st.dv(k);
        if !(t <= s) {
            return Err(format!("delta({}) = {:e} < term {} = {:e}", k, s, nm, t));
        }
        count_name(&mut rep, nm);
    }
    for j in 1..=e {
        for g in (0..=gm).rev() {
            let nm = &c.fnm[j][g];
            let t = single_f_term(&c.st, h, j, g, nm, m, inp);
            let s = c.st.fv(j, g);
            if !(t <= s) {
                return Err(format!("F({}, {}) = {:e} < term {} = {:e}", j, g, s, nm, t));
            }
            if c.st.f[j][g] < ONE {
                rep.worst = rep.worst.max(t / s.max(1e-300));
            }
            count_name(&mut rep, nm);
        }
    }
    Ok(rep)
}
fn dominates(t: &St, s: &St) -> Result<(), String> {
    if t.e != s.e || t.gm != s.gm {
        return Err("T and S_a have different parameters".into());
    }
    for k in 1..=s.e {
        if t.d[k] < s.d[k] {
            return Err(format!("delta_T({}) < delta_a({})", k, k));
        }
        for g in 0..=s.gm {
            if t.f[k][g] < s.f[k][g] {
                return Err(format!("F_T({}, {}) < F_a", k, g));
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------- hand-over rows of Theorem 14.1 of the paper
// The assumption of Theorem 14.1 for a row: E G_h(1) >= c0 mu_h(1) for m1 - 30 < h <= m1 and
// E G_m1(J) >= b1, which a T valid on [a, m1] (a <= m1 - 30) gives when delta_T(1) <= 1 - c0 and
// delta_T(J) <= 1 - b1/mu_m1(J); both thresholds are exact rationals (num, den), compared exactly with
// the grid values.
struct Row {
    name: &'static str,
    m1: i64,
    j: usize,
    t1: (u128, u128),
    tj: (u128, u128),
}
fn row_of(name: &str) -> Row {
    match name {
        // (c0, eps) = (0.85, 0.01), a row that the paper does not use: b1 = 100895.78, 1 - b1/mu_316228(44)
        // rounded down to 0.042955
        "r085" => Row { name: "r085", m1: 316228, j: 44, t1: (3, 20), tj: (42955, 1_000_000) },
        // (c0, eps) = (0.6, 0.02), the row of the paper (Section 14, Proposition 15.1 (2)): b1 = 27290443/50,
        // 1 - b1/mu_1778279(62) = 7045771/88917100 (code/dcheck/dcheck_m1.out)
        "mode1" => Row { name: "mode1", m1: 1_778_279, j: 62, t1: (2, 5), tj: (7_045_771, 88_917_100) },
        _ => panic!("unknown row {} (r085 or mode1)", name),
    }
}
// exact test of the row on T valid on [a, b]; delta_T(min(J, E)) bounds delta_T(J) by Lemma 10.7 (1) of
// the paper
fn handover(t: &St, a: i64, b: i64, r: &Row) -> (bool, String) {
    let kj = r.j.min(t.e);
    let ok1 = (t.d[1] as u128) * r.t1.1 <= r.t1.0 << GRID;
    let okj = (t.d[kj] as u128) * r.tj.1 <= r.tj.0 << GRID;
    let okiv = b == r.m1 && a <= r.m1 - 30;
    let met = ok1 && okj && okiv;
    (
        met,
        format!(
            "row {}: interval [{}, {}] {} [a, {}] with a <= {}; delta_T(1) {:.6} <= {}/{} {}; delta_T({}) {:.6} <= {}/{} {}: {}",
            r.name, a, b, if okiv { "is" } else { "is NOT" }, r.m1, r.m1 - 30, t.dv(1), r.t1.0, r.t1.1, ok1, kj, t.dv(kj), r.tj.0, r.tj.1, okj,
            if met { "MET" } else { "NOT MET" }
        ),
    )
}

// ---------------------------------------------------------------- reading d3-fhat states
// d3-fhat's save_state (absolute deficits at the saved height) or FHAT_SAVET (normalized deficits of T)
fn read_float_state(path: &str, normalized: bool) -> (i64, usize, usize, Vec<f64>, Vec<Vec<f64>>) {
    let txt = fs::read_to_string(path).unwrap();
    let mut it = txt.split_whitespace();
    let h: i64 = it.next().unwrap().parse().unwrap();
    let e: usize = it.next().unwrap().parse().unwrap();
    let gm: usize = it.next().unwrap().parse().unwrap();
    let mut d = vec![0.0f64; e + 1];
    let mut f = vec![vec![1.0f64; gm + 1]; e + 1];
    for k in 0..=e {
        d[k] = it.next().unwrap().parse().unwrap();
        if !normalized && k > 0 {
            d[k] /= (h as f64 + 1.0 + k as f64) / 3.0;
        }
        for g in 0..=gm {
            f[k][g] = it.next().unwrap().parse().unwrap();
        }
    }
    (h, e, gm, d, f)
}

fn usage() -> ! {
    eprintln!(
        "usage:\n  d3-cert seed MASSES M0 E GM OUT\n  d3-cert chain IN OUTDIR HEND VM JM SPINE S4UNTIL EB S4J NTH   (steps from IN's height to HEND, S4 while the child height < S4UNTIL)\n  d3-cert ext IN OUT E2 GM2\n  d3-cert tcheck SA TFILE B VM JM SPINE NTH OUT ROW   (T from fhat FHAT_SAVET, interval [a, B], a = SA's height, ROW r085 or mode1)\n  d3-cert verify MANIFEST [FROM [TO]]\n  d3-cert tostate CERT OUT   (fhat FHAT_LOAD format, absolute deficits)"
    );
    std::process::exit(2)
}

fn to_float_state(c: &Cert, path: &str) {
    let s = &c.st;
    let mut o = format!("{} {} {}\n", s.h, s.e, s.gm);
    for k in 0..=s.e {
        let dabs = if k == 0 { (s.h as f64 + 1.0) / 3.0 } else { s.dv(k) * (s.h as f64 + 1.0 + k as f64) / 3.0 };
        o.push_str(&format!("{:e}", dabs));
        for g in 0..=s.gm {
            o.push_str(&format!(" {:e}", s.fv(k, g)));
        }
        o.push('\n');
    }
    fs::write(path, o).unwrap();
}

fn main() {
    let a: Vec<String> = env::args().collect();
    if a.len() < 2 {
        usage();
    }
    let t0 = std::time::Instant::now();
    match a[1].as_str() {
        "seed" => {
            if a.len() != 7 {
                usage();
            }
            let m0: i64 = a[3].parse().unwrap();
            let e: usize = a[4].parse().unwrap();
            let gm: usize = a[5].parse().unwrap();
            let m = read_masses(&a[2], m0, e);
            let mut c = gen_seed(&m, m0, e, gm);
            c.extra.push(format!("source {}", a[2]));
            write_cert(&c, &a[6]);
            println!("seed at {}: delta(1) {:.6} delta(E) {:.6} F(1, 11) {:.6e}; {:.2} s", m0, c.st.dv(1), c.st.dv(e), c.st.fv(1, 11.min(gm)), t0.elapsed().as_secs_f64());
        }
        "chain" => {
            if a.len() != 12 {
                usage();
            }
            let mut cur = read_cert(&a[2]).st;
            let dir = &a[3];
            let hend: i64 = a[4].parse().unwrap();
            let vm: usize = a[5].parse().unwrap();
            let jm: usize = a[6].parse().unwrap();
            let spine = a[7] == "1";
            let s4until: i64 = a[8].parse().unwrap();
            let eb: usize = a[9].parse().unwrap();
            let s4j: usize = a[10].parse().unwrap();
            let nth: usize = a[11].parse().unwrap();
            fs::create_dir_all(dir).unwrap();
            while cur.h < hend {
                let t1 = std::time::Instant::now();
                let par = Par { vm, jm, spine, s4: cur.h < s4until, eb, s4j };
                let (c, worst) = eval_map(&cur, par, cur.h, cur.h, "STEP", None, nth);
                let path = format!("{}/m{}.cert", dir, c.st.h);
                write_cert(&c, &path);
                let e = c.st.e;
                println!(
                    "{} delta(1) {:.5} delta(12) {:.5} delta(E) {:.5} F(1, 16) {:.4e} F(4, 16) {:.4e} worst {:.12} s4 {} {:.2} s",
                    c.st.h,
                    c.st.dv(1),
                    c.st.dv(12.min(e)),
                    c.st.dv(e),
                    c.st.fv(1, 16.min(c.st.gm)),
                    c.st.fv(4.min(e), 16.min(c.st.gm)),
                    worst,
                    par.s4 as u8,
                    t1.elapsed().as_secs_f64()
                );
                cur = c.st;
            }
        }
        "ext" => {
            if a.len() != 6 {
                usage();
            }
            let inp = read_cert(&a[2]).st;
            let e2: usize = a[4].parse().unwrap();
            let gm2: usize = a[5].parse().unwrap();
            let c = gen_ext(&inp, e2, gm2);
            write_cert(&c, &a[3]);
            println!("ext at {}: E {} -> {}, GM {} -> {}; {:.2} s", inp.h, inp.e, e2, inp.gm, gm2, t0.elapsed().as_secs_f64());
        }
        "tcheck" => {
            if a.len() != 11 {
                usage();
            }
            let sa = read_cert(&a[2]).st;
            let (th, e, gm, td, tf) = read_float_state(&a[3], true);
            let b: i64 = a[4].parse().unwrap();
            assert!(th == sa.h && e == sa.e && gm == sa.gm, "T does not match S_a");
            let mut t = St { h: sa.h, e, gm, f: vec![vec![ONE; gm + 1]; e + 1], d: vec![ONE; e + 1] };
            for k in 1..=e {
                t.d[k] = grid_up(td[k].min(1.0)).max(sa.d[k]);
                for g in 0..=gm {
                    t.f[k][g] = grid_up(tf[k][g].min(1.0)).max(sa.f[k][g]);
                }
                for g in 1..=gm {
                    t.f[k][g] = t.f[k][g].max(t.f[k][g - 1]);
                }
            }
            let par = Par { vm: a[5].parse().unwrap(), jm: a[6].parse().unwrap(), spine: a[7] == "1", s4: false, eb: 0, s4j: 0 };
            let nth: usize = a[8].parse().unwrap();
            let (mut c, worst) = eval_map(&t, par, sa.h, b - 1, "CHECK", Some(&t), nth);
            c.st.h = sa.h;
            let row = row_of(&a[10]);
            let (_, ho) = handover(&c.st, sa.h, b, &row);
            c.extra.push(format!("interval {} {}", sa.h, b));
            c.extra.push(format!("handover {}", ho));
            write_cert(&c, &a[9]);
            println!("tcheck on [{}, {}]: all components named, worst term/stored {:.12}; hand-over {}; {:.2} s", sa.h, b, worst, ho, t0.elapsed().as_secs_f64());
        }
        "dumpmasses" => {
            // test input only: masses from a floating point dump of the M1 rows (CDF h k g F lines), floor(P(x) 2^62)
            let txt = fs::read_to_string(&a[2]).unwrap();
            let m0: i64 = a[3].parse().unwrap();
            let e: usize = a[4].parse().unwrap();
            let v: usize = a[5].parse().unwrap();
            let mut fr = vec![vec![f64::NAN; v]; e + 1];
            for line in txt.lines() {
                let w: Vec<&str> = line.split_whitespace().collect();
                if w.len() >= 5 && w[0] == "CDF" && w[1].parse::<i64>().ok() == Some(m0) {
                    let k: usize = w[2].parse().unwrap();
                    let g: usize = w[3].parse().unwrap();
                    if k <= e && g < v {
                        fr[k][g] = w[4].parse().unwrap();
                    }
                }
            }
            let mut o = format!("# test masses from {} (floating point, not a certified M1 run)\nMASSV {} {}\n", a[2], m0, v);
            for k in 1..=e {
                for x in 1..=v {
                    let p = if x < v { fr[k][x] - fr[k][x - 1] } else { 1.0 - fr[k][v - 1] };
                    assert!(!p.is_nan(), "missing CDF line k {} x {}", k, x);
                    let n = (p.max(0.0) * (2f64).powi(W62)).floor() as u128;
                    o.push_str(&format!("MASS {} {} {} {}\n", m0, k, x, n));
                }
            }
            fs::write(&a[6], o).unwrap();
        }
        "tostate" => {
            let c = read_cert(&a[2]);
            to_float_state(&c, &a[3]);
        }
        "verify" => {
            if a.len() < 3 {
                usage();
            }
            let man = fs::read_to_string(&a[2]).unwrap();
            let base = std::path::Path::new(&a[2]).parent().unwrap().to_path_buf();
            let lines: Vec<&str> = man.lines().filter(|l| !l.trim().is_empty() && !l.starts_with('#')).collect();
            let from: usize = a.get(3).map(|x| x.parse().unwrap()).unwrap_or(0);
            let to: usize = a.get(4).map(|x| x.parse().unwrap()).unwrap_or(lines.len());
            let p = |x: &str| base.join(x).to_string_lossy().to_string();
            let mut fails = 0usize;
            let mut handover_met = false;
            let mut prev_out: Option<String> = None;
            for (i, line) in lines.iter().enumerate().take(to).skip(from) {
                let t1 = std::time::Instant::now();
                let w: Vec<&str> = line.split_whitespace().collect();
                let res: Result<(Report, String), String> = match w[0] {
                    "SEED" => {
                        let c = read_cert(&p(w[2]));
                        let m = read_masses(&p(w[1]), c.st.h, c.st.e);
                        verify_single(&c, Some(&m), None).map(|r| (r, format!("seed at {}", c.st.h)))
                    }
                    "STEP" => {
                        let inp = read_cert(&p(w[1])).st;
                        let c = read_cert(&p(w[2]));
                        if c.kind != "STEP" {
                            Err("not a STEP file".into())
                        } else {
                            verify_step(&c, &inp).map(|r| (r, format!("step {} -> {} (s4 {})", inp.h, c.st.h, c.par.s4 as u8)))
                        }
                    }
                    "EXT" => {
                        let inp = read_cert(&p(w[1])).st;
                        let c = read_cert(&p(w[2]));
                        if c.st.h != inp.h {
                            Err("EXT changes the height".into())
                        } else {
                            verify_single(&c, None, Some(&inp)).map(|r| (r, format!("ext at {}: E {} GM {}", c.st.h, c.st.e, c.st.gm)))
                        }
                    }
                    "CHECK" => {
                        let sa = read_cert(&p(w[1])).st;
                        let c = read_cert(&p(w[2]));
                        let iv: Vec<i64> = c.extra.iter().find(|x| x.starts_with("interval")).map(|x| x.split_whitespace().skip(1).map(|y| y.parse().unwrap()).collect()).unwrap_or_default();
                        let r = (|| -> Result<(Report, String), String> {
                            if iv.len() != 2 || iv[0] != sa.h || c.lo != iv[0] || c.hi != iv[1] - 1 {
                                return Err("interval line does not match S_a and the children range".into());
                            }
                            dominates(&c.st, &sa)?;
                            let mut t = c.st.clone();
                            t.h = sa.h;
                            if c.par.s4 {
                                return Err("the interval check with the S4 terms is not part of this route".into());
                            }
                            let rep = verify_step(&Cert { kind: "CHECK".into(), lo: c.lo, hi: c.hi, par: c.par, st: t.clone(), dn: c.dn.clone(), fnm: c.fnm.clone(), extra: Vec::new() }, &t)?;
                            let row = row_of(w.get(3).copied().unwrap_or("r085"));
                            let (met, ho) = handover(&t, iv[0], iv[1], &row);
                            if met {
                                handover_met = true;
                            }
                            Ok((rep, format!("interval check on [{}, {}], T >= S_a; hand-over (exact comparisons) {}", iv[0], iv[1], ho)))
                        })();
                        r
                    }
                    _ => Err(format!("unknown manifest line {}", line)),
                };
                // the manifest must be one chain: each line reads the file the line before wrote
                let res = match res {
                    Ok(_) if i > from && w[0] != "SEED" && w.get(1).copied() != prev_out.as_deref() => {
                        Err(format!("input {} is not the output {:?} of the line before", w.get(1).unwrap_or(&""), prev_out))
                    }
                    other => other,
                };
                prev_out = w.get(2).map(|x| x.to_string());
                match res {
                    Ok((rep, what)) => {
                        let names: Vec<String> = rep.counts.iter().map(|(k, v)| format!("{}:{}", k, v)).collect();
                        println!("{} OK {}; largest term/stored {:.12}; names {}; {:.2} s", i, what, rep.worst, names.join(" "), t1.elapsed().as_secs_f64());
                    }
                    Err(e) => {
                        fails += 1;
                        println!("{} FAIL {}: {}", i, line, e);
                    }
                }
            }
            let whole = from == 0 && to >= lines.len() && lines.first().map(|l| l.starts_with("SEED")).unwrap_or(false);
            println!(
                "verify: {} lines checked, {} failed: {}; {}; {:.1} s",
                to.min(lines.len()) - from.min(lines.len()),
                fails,
                if fails == 0 { "PASS" } else { "FAIL" },
                if whole && fails == 0 && handover_met { "the whole manifest from the seed, ending in a check whose hand-over is MET: (CertS) holds" } else { "not a complete (CertS) (a range, no seed, or no hand-over met)" },
                t0.elapsed().as_secs_f64()
            );
            if fails > 0 {
                std::process::exit(1);
            }
        }
        _ => usage(),
    }
}
