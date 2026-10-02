// Exact objects of code/certificate/FORMAT.md, version 4: the table (version 3), the child chain
// with its max chains and potentials, the states and their moves and stops with the roundings to 48 bits,
// the compositions C_q, and SHA-256. Used by the generator and its exact check.
pub mod sha256;

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::collections::HashMap;

pub type Q = BigRational;

pub const WBITS: u32 = 48; // fractional bits of the rounded weights
pub const VBITS: u32 = 40; // fractional bits of V' and W'
pub const NONE: u32 = u32::MAX;

pub fn qi(n: i64) -> Q {
    Q::from_integer(BigInt::from(n))
}

/// A number of FORMAT "Lines": a nonnegative decimal integer or a/b, nothing else.
pub fn parse_q(s: &str) -> Result<Q, String> {
    let dec = |t: &str| -> Result<BigInt, String> {
        if t.is_empty() || !t.bytes().all(|b| b.is_ascii_digit()) {
            return Err(format!("not a decimal integer: {:?}", s));
        }
        Ok(t.parse::<BigInt>().unwrap())
    };
    match s.split_once('/') {
        Some((a, b)) => {
            let (a, b) = (dec(a)?, dec(b)?);
            if b.is_zero() {
                return Err(format!("zero denominator: {}", s));
            }
            Ok(Q::new(a, b))
        }
        None => Ok(Q::from_integer(dec(s)?)),
    }
}

pub fn qpow(x: &Q, k: usize) -> Q {
    let mut r = Q::one();
    for _ in 0..k {
        r = &r * x;
    }
    r
}

/// floor(2^k q) and ceil(2^k q) for q >= 0.
pub fn floor2(q: &Q, k: u32) -> BigInt {
    (q.numer() << k as usize).div_floor(q.denom())
}
pub fn ceil2(q: &Q, k: u32) -> BigInt {
    (q.numer() << k as usize).div_ceil(q.denom())
}

/// A fraction n / d with d > 0, kept unreduced (products without gcd).
#[derive(Clone, Debug)]
pub struct Fr {
    pub n: BigInt,
    pub d: BigInt,
}
impl Fr {
    pub fn of(q: &Q) -> Fr {
        Fr { n: q.numer().clone(), d: q.denom().clone() }
    }
    pub fn mul(&self, o: &Fr) -> Fr {
        Fr { n: &self.n * &o.n, d: &self.d * &o.d }
    }
    pub fn mul_int(&self, m: u64) -> Fr {
        Fr { n: &self.n * BigInt::from(m), d: self.d.clone() }
    }
    /// ceil(2^48 x) for x >= 0
    pub fn ceil48(&self) -> u128 {
        let v = (&self.n << WBITS as usize).div_ceil(&self.d);
        v.to_u128().expect("rounded stop weight beyond u128")
    }
}

// ---------------------------------------------------------------- the table (version 3)

pub struct Table {
    pub d: usize,
    pub j: usize,
    pub t: usize,
    pub tp: usize,
    pub eps: Q,
    pub rho: Q,
    pub phi: Q,
    pub kappa: Q,
    /// labels[q] for q = 1..J-1 in the order of the label lines; labels[0] = [root], labels[J] = [end]
    pub labels: Vec<Vec<String>>,
    /// tr[q]: (from, delta, to, P), in file order
    pub tr: Vec<Vec<(String, usize, String, Q)>>,
    /// errors of (I1) well-formedness found while reading
    pub errors: Vec<String>,
    pub has_h: bool,
}

pub fn read_table(text: &str) -> Result<Table, String> {
    let mut tb = Table {
        d: 4,
        j: 0,
        t: 0,
        tp: usize::MAX,
        eps: Q::zero(),
        rho: Q::zero(),
        phi: Q::zero(),
        kappa: Q::zero(),
        labels: Vec::new(),
        tr: Vec::new(),
        errors: Vec::new(),
        has_h: false,
    };
    let mut labs: Vec<(usize, String)> = Vec::new();
    let mut trs: Vec<(usize, String, usize, String, Q)> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for (ln, l) in text.lines().enumerate() {
        let w: Vec<&str> = l.split_whitespace().collect();
        if w.is_empty() || w[0].starts_with('#') {
            continue;
        }
        let bad = |m: &str| format!("table line {}: {}: {}", ln + 1, m, l);
        let int = |s: &str| -> Result<usize, String> { s.parse::<usize>().map_err(|_| bad("integer expected")) };
        let need = |n: usize| -> Result<(), String> { if w.len() == n { Ok(()) } else { Err(bad("wrong number of tokens")) } };
        if !seen.insert(w[0].to_string()) && !matches!(w[0], "label" | "tr" | "h" | "plan") {
            return Err(bad("repeated keyword"));
        }
        match w[0] {
            "d" => { need(2)?; tb.d = int(w[1])? }
            "J" => { need(2)?; tb.j = int(w[1])? }
            "T" => { need(2)?; tb.t = int(w[1])? }
            "Tpend" => { need(2)?; tb.tp = int(w[1])? }
            "eps" => { need(2)?; tb.eps = parse_q(w[1])? }
            "rho" => { need(2)?; tb.rho = parse_q(w[1])? }
            "phi" => { need(2)?; tb.phi = parse_q(w[1])? }
            "kappa" => { need(2)?; tb.kappa = parse_q(w[1])? }
            "rounds" | "prune" => {}
            "label" => { need(3)?; labs.push((int(w[1])?, w[2].to_string())) }
            "tr" => { need(6)?; trs.push((int(w[1])?, w[2].to_string(), int(w[3])?, w[4].to_string(), parse_q(w[5])?)) }
            "h" | "plan" => tb.has_h = true,
            _ => return Err(bad("unknown keyword")),
        }
    }
    if tb.tp == usize::MAX {
        tb.tp = tb.t;
    }
    let j = tb.j;
    if j < 2 {
        return Err(format!("J = {} < 2", j));
    }
    tb.labels = vec![Vec::new(); j + 1];
    tb.labels[0].push("root".into());
    tb.labels[j].push("end".into());
    for (q, n) in labs {
        if q < 1 || q > j - 1 {
            tb.errors.push(format!("label {} {} at a level outside 1..J-1", q, n));
        } else if n == "root" || n == "end" {
            tb.errors.push(format!("label named {}", n));
        } else if tb.labels[q].contains(&n) {
            tb.errors.push(format!("label {} {} declared twice", q, n));
        } else {
            tb.labels[q].push(n);
        }
    }
    tb.tr = vec![Vec::new(); j];
    let mut keys = std::collections::HashSet::new();
    for (q, a, dl, b, p) in trs {
        if q >= j {
            tb.errors.push(format!("tr at level {} >= J", q));
            continue;
        }
        if !tb.labels[q].contains(&a) || !tb.labels[q + 1].contains(&b) {
            tb.errors.push(format!("tr {} {} {} {}: undeclared label", q, a, dl, b));
            continue;
        }
        if !p.is_positive() {
            tb.errors.push(format!("tr {} {} {} {}: P not > 0", q, a, dl, b));
        }
        if !keys.insert((q, a.clone(), dl, b.clone())) {
            tb.errors.push(format!("tr {} {} {} {}: repeated", q, a, dl, b));
        }
        tb.tr[q].push((a, dl, b, p));
    }
    // every row sums to 1; root and every target label below level J have transitions
    for q in 0..j {
        for l in &tb.labels[q] {
            let s: Q = tb.tr[q].iter().filter(|x| &x.0 == l).map(|x| x.3.clone()).fold(Q::zero(), |a, b| a + b);
            let used = q == 0 || tb.tr[q - 1].iter().any(|x| &x.2 == l);
            if s != Q::one() && (used || s != Q::zero()) {
                tb.errors.push(format!("row {} {} sums to {}", q, l, s));
            }
            if q > 0 && !used && s.is_zero() {
                // a declared label nobody reaches and with no transitions: harmless, but recorded
                tb.errors.push(format!("label {} {} unused and without transitions", q, l));
            }
        }
    }
    Ok(tb)
}

/// The finite part of H*: atoms B (cumulative vectors) with mass (1 - eps) P_tab(B).
pub fn hstar(tb: &Table) -> Vec<(Vec<u32>, Q)> {
    let mut cur: Vec<(String, Vec<u32>, Q)> = vec![("root".into(), Vec::new(), Q::one() - &tb.eps)];
    for q in 0..tb.j {
        let mut nx = Vec::new();
        for (l, b, m) in &cur {
            for r in tb.tr[q].iter().filter(|x| &x.0 == l) {
                let mut b2 = b.clone();
                b2.push(b.last().copied().unwrap_or(0) + r.1 as u32);
                nx.push((r.2.clone(), b2, m * &r.3));
            }
        }
        cur = nx;
    }
    let mut h: HashMap<Vec<u32>, Q> = HashMap::new();
    for (_, b, m) in cur {
        let e = h.entry(b).or_insert_with(Q::zero);
        *e = &*e + m;
    }
    let mut v: Vec<(Vec<u32>, Q)> = h.into_iter().collect();
    v.sort();
    v
}

/// r_q(S) = sum P phi^delta r_{q+1}(S2), r_J(end) = 1.
pub fn potentials_r(tb: &Table) -> Vec<HashMap<String, Q>> {
    let j = tb.j;
    let mut r: Vec<HashMap<String, Q>> = vec![HashMap::new(); j + 1];
    r[j].insert("end".into(), Q::one());
    for q in (0..j).rev() {
        for l in tb.labels[q].clone() {
            let mut s = Q::zero();
            for x in tb.tr[q].iter().filter(|x| x.0 == l) {
                s += &x.3 * qpow(&tb.phi, x.1) * &r[q + 1][&x.2];
            }
            r[q].insert(l, s);
        }
    }
    r
}

pub struct TableVerdict {
    pub i1: bool,
    pub i2: bool,
    pub i5: bool,
    pub lines: Vec<String>,
    pub theta: Q,
    pub m: Q,
}

/// (I1), (I2), (I5) of a version 3 table, exactly.
pub fn check_table(tb: &Table) -> TableVerdict {
    let mut lines = Vec::new();
    let (eps, rho, phi, kappa) = (&tb.eps, &tb.rho, &tb.phi, &tb.kappa);
    let mut i1 = tb.errors.is_empty() && !tb.has_h;
    for e in &tb.errors {
        lines.push(format!("(I1) table error: {}", e));
    }
    if tb.has_h {
        lines.push("(I1) table has h or plan lines".into());
    }
    if tb.d != 4 {
        i1 = false;
        lines.push(format!("(I1) d = {} (version 4 needs d = 4)", tb.d));
    }
    if tb.tp < tb.t || tb.t < 1 {
        i1 = false;
        lines.push(format!("(I1) T = {}, T' = {}", tb.t, tb.tp));
    }
    let one = Q::one();
    let cond = [
        (eps >= &Q::zero() && eps < &one, "eps in [0, 1)"),
        (rho > &Q::zero() && rho < &one, "rho in (0, 1)"),
        (phi > &one, "phi > 1"),
        (kappa > &one, "kappa > 1"),
    ];
    for (ok, what) in cond {
        if !ok {
            i1 = false;
            lines.push(format!("(I1) fails: {}", what));
        }
    }
    let h = hstar(tb);
    let sh: Q = h.iter().map(|x| x.1.clone()).fold(Q::zero(), |a, b| a + b);
    let tot = &sh + eps;
    if tot != one || h.iter().any(|x| x.1.is_negative()) {
        i1 = false;
    }
    lines.push(format!("(I1) {} atoms in the finite part, sum h + eps - 1 = {}; {}", h.len(), &tot - &one, if i1 { "holds" } else { "FAILS" }));
    // (I2)
    let theta = qi(5) * phi - qi(4) * kappa;
    let pr = phi * rho;
    let mut i2 = pr < one;
    let r = potentials_r(tb);
    let m = if i2 {
        (&one - eps) * &r[0]["root"] + eps * (&one - rho) * qpow(phi, tb.t + 1) / (&one - &pr)
    } else {
        Q::zero()
    };
    let kj = qpow(kappa, tb.j);
    let a = kj >= m;
    let b = &theta * rho >= one;
    i2 = i2 && a && b;
    lines.push(format!(
        "(I2) phi rho < 1: {}; kappa^J - M = {} (~{:.6e}): {}; theta rho - 1 = {} (~{:.6e}): {}; {}",
        pr < one,
        &kj - &m,
        f(&(&kj - &m)),
        a,
        &theta * rho - &one,
        f(&(&theta * rho - &one)),
        b,
        if i2 { "holds" } else { "FAILS" }
    ));
    // (I5)
    let eb1: Q = tb.tr[0].iter().map(|x| &x.3 * qi(x.1 as i64)).fold(Q::zero(), |a, b| a + b);
    let c = (&one - eps) * eb1 + eps * (qi(tb.t as i64 + 1) + rho / (&one - rho));
    let i5 = c < one;
    lines.push(format!("(I5) c = {} (~{:.10}): {}", c, f(&c), if i5 { "holds" } else { "FAILS" }));
    TableVerdict { i1, i2, i5, lines, theta, m }
}

pub fn f(q: &Q) -> f64 {
    // a float view of an exact rational (printing and floating-point candidates only):
    // the quotient scaled to 64 significant bits, then the exponent put back
    if q.is_zero() {
        return 0.0;
    }
    let (n, d) = (q.numer().abs(), q.denom().clone());
    let e = n.bits() as i64 - d.bits() as i64;
    let sh = 64 - e;
    let qq = if sh >= 0 { (&n << sh as usize) / &d } else { &n / (&d << (-sh) as usize) };
    let v = qq.to_f64().unwrap() * 2f64.powi(-(sh as i32));
    if q.is_negative() { -v } else { v }
}

// ---------------------------------------------------------------- the child chain

pub struct Trans {
    pub p: Q,
    pub delta: usize,
    pub next: u8,
}

pub struct Chain {
    pub names: Vec<String>,
    pub idx: HashMap<String, u8>,
    pub rows: Vec<Vec<Trans>>,
    pub lump: Vec<u8>,
    pub w: Vec<Q>,
    pub tail_of: [u8; 2], // c_t for F and for B
    pub labelled: Vec<bool>,
    pub theta: Q,
}

pub fn build_chain(tb: &Table) -> Chain {
    let j = tb.j;
    let mut names: Vec<String> = vec!["F".into(), "B".into()];
    for q in 1..j {
        for l in &tb.labels[q] {
            names.push(format!("{}:{}", q, l));
        }
    }
    for q in 1..j {
        names.push(format!("{}:tail", q));
    }
    for q in 1..j {
        names.push(format!("{}:M", q));
    }
    assert!(names.len() < 128);
    let idx: HashMap<String, u8> = names.iter().enumerate().map(|(i, n)| (n.clone(), i as u8)).collect();
    let lab = |q: usize, l: &str| -> u8 { if q == j { 1 } else { idx[&format!("{}:{}", q, l)] } };
    let tl = |q: usize| -> u8 { if q == j { 1 } else { idx[&format!("{}:tail", q)] } };
    let mm = |q: usize| -> u8 { if q == j { 1 } else { idx[&format!("{}:M", q)] } };
    let n = names.len();
    let mut rows: Vec<Vec<Trans>> = (0..n).map(|_| Vec::new()).collect();
    let one = Q::one();
    let ome = &one - &tb.eps;
    for r in &tb.tr[0] {
        rows[1].push(Trans { p: &ome * &r.3, delta: r.1, next: lab(1, &r.2) });
        if j == 2 {
            // F: root -> S1 -> end; the second index is level 1 -> 2 = J
        }
        for r2 in tb.tr[1].iter().filter(|x| x.0 == r.2) {
            rows[0].push(Trans { p: &ome * &r.3 * &r2.3, delta: r.1 + r2.1, next: lab(2, &r2.2) });
        }
    }
    for q in 1..j {
        for r in &tb.tr[q] {
            rows[lab(q, &r.0) as usize].push(Trans { p: r.3.clone(), delta: r.1, next: lab(q + 1, &r.2) });
        }
        rows[tl(q) as usize].push(Trans { p: one.clone(), delta: 0, next: tl(q + 1) });
        // max chain of level q: tau(k) = max over the labels of level q of P(delta >= k)
        let dmax = tb.tr[q].iter().map(|x| x.1).max().unwrap_or(0);
        let mut tau: Vec<Q> = vec![Q::zero(); dmax + 2];
        for l in &tb.labels[q] {
            for k in 0..=dmax {
                let s: Q = tb.tr[q].iter().filter(|x| &x.0 == l && x.1 >= k).map(|x| x.3.clone()).fold(Q::zero(), |a, b| a + b);
                if s > tau[k] {
                    tau[k] = s;
                }
            }
        }
        for k in 0..=dmax {
            let pk = &tau[k] - &tau[k + 1];
            if pk.is_positive() {
                rows[mm(q) as usize].push(Trans { p: pk, delta: k, next: mm(q + 1) });
            }
        }
    }
    // potentials
    let r = potentials_r(tb);
    let (phi, kappa) = (&tb.phi, &tb.kappa);
    let mut rm: Vec<Q> = vec![Q::one(); j + 1];
    for q in (1..j).rev() {
        let mut s = Q::zero();
        for x in &rows[mm(q) as usize] {
            s += &x.p * qpow(phi, x.delta) * &rm[q + 1];
        }
        rm[q] = s;
    }
    let mut w = vec![Q::zero(); n];
    w[0] = qpow(kappa, j);
    w[1] = qpow(kappa, j - 1);
    for q in 1..j {
        for l in &tb.labels[q] {
            w[lab(q, l) as usize] = qpow(kappa, q - 1) * &r[q][l];
        }
        w[tl(q) as usize] = qpow(kappa, q - 1);
        w[mm(q) as usize] = qpow(kappa, q - 1) * &rm[q];
    }
    let mut lump: Vec<u8> = (0..n as u8).collect();
    let mut labelled = vec![false; n];
    for q in 1..j {
        for l in &tb.labels[q] {
            lump[lab(q, l) as usize] = mm(q);
            labelled[lab(q, l) as usize] = true;
        }
    }
    let theta = qi(5) * phi - qi(4) * kappa;
    let tail_of = [tl(2), tl(1)];
    Chain { names, idx: idx.clone(), rows, lump, w, tail_of, labelled, theta }
}

// ---------------------------------------------------------------- compositions

pub struct Comps {
    /// c[q] for q = 1..=J (c[0] unused): the vectors (x_q..x_J), sum <= T, lexicographic
    pub c: Vec<Vec<Vec<u8>>>,
    pub len: Vec<usize>,
    /// dec[q][i]: index of x - e_q (x_q >= 1), else NONE
    pub dec: Vec<Vec<u32>>,
    /// nx[f][q][i]: if x_q = f, index of (x_{q+1}..x_J) in C_{q+1}, else NONE (q < J)
    pub nx: [Vec<Vec<u32>>; 2],
}

pub fn comps(j: usize, t: usize) -> Comps {
    let gen = |m: usize| -> Vec<Vec<u8>> {
        let mut res: Vec<Vec<u8>> = vec![Vec::new()];
        for _ in 0..m {
            let mut nx = Vec::new();
            for v in &res {
                let s: usize = v.iter().map(|x| *x as usize).sum();
                for d in 0..=(t - s) {
                    let mut w = v.clone();
                    w.push(d as u8);
                    nx.push(w);
                }
            }
            res = nx;
        }
        res
    };
    let mut c = vec![Vec::new(); j + 2];
    for q in 1..=j + 1 {
        c[q] = gen(j + 1 - q);
    }
    let idx: Vec<HashMap<Vec<u8>, u32>> = c.iter().map(|v| v.iter().enumerate().map(|(a, b)| (b.clone(), a as u32)).collect()).collect();
    let len: Vec<usize> = c.iter().map(|v| v.len()).collect();
    let mut dec = vec![Vec::new(); j + 1];
    let mut nx0 = vec![Vec::new(); j + 1];
    let mut nx1 = vec![Vec::new(); j + 1];
    for q in 1..=j {
        for x in &c[q] {
            dec[q].push(if x[0] >= 1 {
                let mut y = x.clone();
                y[0] -= 1;
                idx[q][&y]
            } else {
                NONE
            });
            if q < j {
                let rest = x[1..].to_vec();
                nx0[q].push(if x[0] == 0 { idx[q + 1][&rest] } else { NONE });
                nx1[q].push(if x[0] == 1 { idx[q + 1][&rest] } else { NONE });
            }
        }
    }
    Comps { c, len, dec, nx: [nx0, nx1] }
}

pub fn binom(n: usize, k: usize) -> usize {
    let mut r = 1usize;
    for i in 0..k {
        r = r * (n - i) / (i + 1);
    }
    r
}

// ---------------------------------------------------------------- states and moves

/// key of a state (q, sorted multiset, p): 3 bits q, 4 x 7 bits, 7 bits p
pub fn key(q: usize, s: &[u8; 4], p: usize) -> u64 {
    let mut k = q as u64;
    for c in s {
        k = (k << 7) | *c as u64;
    }
    (k << 7) | p as u64
}
pub fn unkey(k: u64) -> (usize, [u8; 4], usize) {
    let p = (k & 127) as usize;
    let mut r = k >> 7;
    let mut s = [0u8; 4];
    for i in (0..4).rev() {
        s[i] = (r & 127) as u8;
        r >>= 7;
    }
    (r as usize, s, p)
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Out {
    Stop,
    Abs,
    /// the reached state (phase, sorted multiset, pending), before the flag rule
    Reach(usize, [u8; 4], usize),
}

#[derive(Clone, Copy, Debug)]
pub struct Move {
    pub lo: u64, // floor(2^48 omega)
    pub hi: u64, // ceil(2^48 omega); for the exit ceil(2^48 theta / 5)
    pub f: u8,
    pub out: Out,
    pub stop_hi: u128, // a stop p' > T': ceil(2^48 x its weight)
}

pub struct StateStops {
    pub e0_hi: u128, // exit stop at budget 0, rounded up
    pub cf_hi: u128, // closed-form tails, each rounded up, summed
    pub pp_hi: u128, // stops p' > T', each rounded up, summed
    pub n_stops: usize,
}

pub struct Ctx {
    pub j: usize,
    pub t: usize,
    pub tp: usize,
    pub nch: usize,
    pub exit_lo: u64,
    pub exit_hi: u64,
    pub exit_hi_omega: u64, // ceil(2^48 / 5), the scalar exit weight rounded up (for Z only)
    pub row_lo: Vec<Vec<[u64; 5]>>,
    pub row_hi: Vec<Vec<[u64; 5]>>,
    pub row_om: Vec<Vec<Q>>,       // P / 5
    pub tail_lo: Vec<[u64; 5]>,     // by t - T - 1
    pub tail_hi: Vec<[u64; 5]>,
    pub tail_om: Vec<Q>,             // eps (1 - rho) rho^(t-T-1) / 5
    pub phipow: Vec<Fr>,
    pub cf: Vec<Fr>,                 // by t0: (1/5) eps (1 - rho) rho^(t0-T-1) phi^t0 / (1 - phi rho)
    pub theta5: Fr,
    pub wfr: Vec<Fr>,
    pub chain: Chain,
}

impl Ctx {
    pub fn new(tb: &Table, chain: Chain) -> Ctx {
        let five = qi(5);
        let r48 = |q: &Q| -> (u64, u64) { (floor2(q, WBITS).to_u64().unwrap(), ceil2(q, WBITS).to_u64().unwrap()) };
        let one = Q::one();
        let mut row_lo = Vec::new();
        let mut row_hi = Vec::new();
        let mut row_om = Vec::new();
        for row in &chain.rows {
            let mut lo = Vec::new();
            let mut hi = Vec::new();
            let mut om = Vec::new();
            for tr in row {
                let o = &tr.p / &five;
                let mut a = [0u64; 5];
                let mut b = [0u64; 5];
                for m in 1..=4 {
                    let (x, y) = r48(&(&o * qi(m as i64)));
                    a[m] = x;
                    b[m] = y;
                }
                lo.push(a);
                hi.push(b);
                om.push(o);
            }
            row_lo.push(lo);
            row_hi.push(hi);
            row_om.push(om);
        }
        let (t, tp) = (tb.t, tb.tp);
        let mut tail_lo = Vec::new();
        let mut tail_hi = Vec::new();
        let mut tail_om = Vec::new();
        for k in 0..=tp {
            let o = &tb.eps * (&one - &tb.rho) * qpow(&tb.rho, k) / &five;
            let mut a = [0u64; 5];
            let mut b = [0u64; 5];
            for m in 1..=4 {
                let (x, y) = r48(&(&o * qi(m as i64)));
                a[m] = x;
                b[m] = y;
            }
            tail_lo.push(a);
            tail_hi.push(b);
            tail_om.push(o);
        }
        let maxd = chain.rows.iter().flatten().map(|x| x.delta).max().unwrap_or(0);
        let phipow: Vec<Fr> = (0..=(tp + maxd + tb.j + t + 4)).map(|k| Fr::of(&qpow(&tb.phi, k))).collect();
        let mut cf = vec![Fr::of(&Q::zero()); tp + 3];
        for t0 in (t + 1)..=(tp + 2) {
            let v = &tb.eps * (&one - &tb.rho) * qpow(&tb.rho, t0 - t - 1) * qpow(&tb.phi, t0) / (&one - &tb.phi * &tb.rho) / &five;
            cf[t0] = Fr::of(&v);
        }
        let th5 = &chain.theta / &five;
        let (exit_lo, _) = r48(&(&one / &five));
        let (_, exit_hi_omega) = r48(&(&one / &five));
        let (_, exit_hi) = r48(&th5);
        let wfr = chain.w.iter().map(Fr::of).collect();
        Ctx {
            j: tb.j,
            t,
            tp,
            nch: chain.names.len(),
            exit_lo,
            exit_hi,
            exit_hi_omega,
            row_lo,
            row_hi,
            row_om,
            tail_lo,
            tail_hi,
            tail_om,
            phipow,
            cf,
            theta5: Fr::of(&th5),
            wfr,
            chain,
        }
    }

    pub fn wprod(&self, s: &[u8; 4], cache: &mut HashMap<[u8; 4], Fr>) -> Fr {
        if let Some(x) = cache.get(s) {
            return x.clone();
        }
        let mut r = self.wfr[s[0] as usize].clone();
        for c in &s[1..] {
            r = r.mul(&self.wfr[*c as usize]);
        }
        cache.insert(*s, r.clone());
        r
    }

    /// Every move of the state (q, s, p) (s sorted), and its stops, as in FORMAT v4
    /// "Moves and stops of a state". Stops p' > T' are moves with out = Stop.
    pub fn moves(&self, q: usize, s: &[u8; 4], p: usize, with_stops: bool, cache: &mut HashMap<[u8; 4], Fr>, mv: &mut Vec<Move>) -> StateStops {
        mv.clear();
        let (j, t, tp) = (self.j, self.t, self.tp);
        let reach = |s2: [u8; 4], p2: usize| -> Out {
            if p2 == 0 {
                if q == j { Out::Abs } else { Out::Reach(q + 1, s2, 1) }
            } else {
                Out::Reach(q, s2, p2)
            }
        };
        // the exit
        mv.push(Move { lo: self.exit_lo, hi: self.exit_hi, f: 1, out: reach(*s, p - 1), stop_hi: 0 });
        let mut st = StateStops { e0_hi: 0, cf_hi: 0, pp_hi: 0, n_stops: 0 };
        if with_stops {
            st.e0_hi = self.theta5.mul(&self.phipow[p - 1 + j - q]).mul(&self.wprod(s, cache)).ceil48();
            st.n_stops += 1;
        }
        for a in 0..4 {
            if a > 0 && s[a] == s[a - 1] {
                continue;
            }
            let c = s[a] as usize;
            let m = s.iter().filter(|&&x| x as usize == c).count();
            let repl = |nx: u8| -> [u8; 4] {
                let mut s2 = *s;
                s2[a] = nx;
                s2.sort_unstable();
                s2
            };
            for (i, tr) in self.chain.rows[c].iter().enumerate() {
                let s2 = repl(tr.next);
                let p2 = p - 1 + tr.delta;
                if p2 > tp {
                    let mut sh = 0;
                    if with_stops {
                        let om = Fr::of(&(&self.row_om[c][i] * qi(m as i64)));
                        sh = om.mul(&self.phipow[p2 + j - q]).mul(&self.wprod(&s2, cache)).ceil48();
                        st.pp_hi += sh;
                        st.n_stops += 1;
                    }
                    mv.push(Move { lo: self.row_lo[c][i][m], hi: self.row_hi[c][i][m], f: 0, out: Out::Stop, stop_hi: sh });
                } else {
                    mv.push(Move { lo: self.row_lo[c][i][m], hi: self.row_hi[c][i][m], f: 0, out: reach(s2, p2), stop_hi: 0 });
                }
            }
            if c < 2 {
                let ct = self.chain.tail_of[c];
                let s2 = repl(ct);
                // tail atoms T + 1 <= tt <= T' - p + 1
                let mut tt = t + 1;
                while tt + p <= tp + 1 {
                    let k = tt - t - 1;
                    mv.push(Move { lo: self.tail_lo[k][m], hi: self.tail_hi[k][m], f: 0, out: reach(s2, p - 1 + tt), stop_hi: 0 });
                    tt += 1;
                }
                if with_stops {
                    let t0 = (t + 1).max(tp + 2 - p);
                    st.cf_hi += self.cf[t0].mul_int(m as u64).mul(&self.phipow[p - 1 + j - q]).mul(&self.wprod(&s2, cache)).ceil48();
                    st.n_stops += 1;
                }
            }
        }
        st
    }

    pub fn lump(&self, s: &[u8; 4]) -> [u8; 4] {
        let mut s2 = [0u8; 4];
        for i in 0..4 {
            s2[i] = self.chain.lump[s[i] as usize];
        }
        s2.sort_unstable();
        s2
    }
    pub fn has_label(&self, s: &[u8; 4]) -> bool {
        s.iter().any(|c| self.chain.labelled[*c as usize])
    }
}

/// an exact max flow from the supplies (atoms x, integer capacities) into the receivers (atoms y,
/// integer capacities) along x -> y for x <= y componentwise; Dinic on big integers
pub fn maxflow_big(sup: &[(Vec<u32>, BigInt)], rec: &[(Vec<u32>, BigInt)]) -> (BigInt, Vec<(usize, usize, BigInt)>) {
    let (nx, ny) = (sup.len(), rec.len());
    let (src, snk) = (0usize, 1usize);
    let n = 2 + nx + ny;
    let mut to: Vec<usize> = Vec::new();
    let mut cp: Vec<BigInt> = Vec::new();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    let add = |a: usize, b: usize, c: BigInt, to: &mut Vec<usize>, cp: &mut Vec<BigInt>, adj: &mut Vec<Vec<usize>>| {
        adj[a].push(to.len());
        to.push(b);
        cp.push(c);
        adj[b].push(to.len());
        to.push(a);
        cp.push(BigInt::zero());
    };
    let inf: BigInt = sup.iter().map(|x| x.1.clone()).fold(BigInt::one(), |a, b| a + b);
    for (i, (_, s)) in sup.iter().enumerate() {
        add(src, 2 + i, s.clone(), &mut to, &mut cp, &mut adj);
    }
    for (k, (_, c)) in rec.iter().enumerate() {
        add(2 + nx + k, snk, c.clone(), &mut to, &mut cp, &mut adj);
    }
    let mut mid = Vec::new();
    for (i, (x, _)) in sup.iter().enumerate() {
        for (k, (y, _)) in rec.iter().enumerate() {
            if x.iter().zip(y.iter()).all(|(a, b)| a <= b) {
                mid.push((i, k, to.len()));
                add(2 + i, 2 + nx + k, inf.clone(), &mut to, &mut cp, &mut adj);
            }
        }
    }
    let mut total = BigInt::zero();
    loop {
        let mut level = vec![-1i32; n];
        level[src] = 0;
        let mut qu = std::collections::VecDeque::new();
        qu.push_back(src);
        while let Some(u) = qu.pop_front() {
            for &e in &adj[u] {
                if cp[e].is_positive() && level[to[e]] < 0 {
                    level[to[e]] = level[u] + 1;
                    qu.push_back(to[e]);
                }
            }
        }
        if level[snk] < 0 {
            break;
        }
        let mut it = vec![0usize; n];
        // iterative DFS for blocking flow
        loop {
            let mut path: Vec<usize> = Vec::new();
            let mut u = src;
            let found = loop {
                if u == snk {
                    break true;
                }
                let mut adv = false;
                while it[u] < adj[u].len() {
                    let e = adj[u][it[u]];
                    let v = to[e];
                    if cp[e].is_positive() && level[v] == level[u] + 1 {
                        path.push(e);
                        u = v;
                        adv = true;
                        break;
                    }
                    it[u] += 1;
                }
                if !adv {
                    if u == src {
                        break false;
                    }
                    level[u] = -1; // dead end
                    let e = path.pop().unwrap();
                    u = to[e ^ 1];
                    it[u] += 1;
                }
            };
            if !found {
                break;
            }
            let mut b = cp[path[0]].clone();
            for &e in &path {
                if cp[e] < b {
                    b = cp[e].clone();
                }
            }
            for &e in &path {
                cp[e] -= &b;
                cp[e ^ 1] += &b;
            }
            total += b;
        }
    }
    let flows = mid.into_iter().map(|(i, k, e)| (i, k, cp[e ^ 1].clone())).filter(|x| x.2.is_positive()).collect();
    (total, flows)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn rounding() {
        let q = parse_q("1/5").unwrap();
        // 2^48 / 5 = 56294995342131.2
        assert_eq!(floor2(&q, 48), BigInt::from(56294995342131u64));
        assert_eq!(ceil2(&q, 48), BigInt::from(56294995342132u64));
        let e = parse_q("3/4").unwrap();
        assert_eq!(floor2(&e, 2), BigInt::from(3));
        assert_eq!(ceil2(&e, 2), BigInt::from(3));
        assert!(parse_q("-1/2").is_err() && parse_q("1.5").is_err() && parse_q("1/0").is_err() && parse_q("1e3").is_err());
        assert_eq!(Fr::of(&q).mul_int(5).ceil48(), 1u128 << 48);
        assert!((f(&parse_q("3/1267650600228229401496703205376").unwrap()) - 3.0 * 2f64.powi(-100)).abs() < 1e-45);
    }
    #[test]
    fn compositions() {
        let c = comps(4, 8);
        assert_eq!(&c.len[1..=5], &[495, 165, 45, 9, 1]);
        for q in 1..=4 {
            assert_eq!(c.len[q], binom(8 + 4 - q + 1, 4 - q + 1));
            // lexicographic, first coordinate most significant
            assert!(c.c[q].windows(2).all(|w| w[0] < w[1]));
        }
        assert_eq!(c.c[1][1], vec![0, 0, 0, 1]);
        assert_eq!(c.dec[1][c.c[1].iter().position(|x| x == &vec![2, 0, 1, 0]).unwrap()] as usize, c.c[1].iter().position(|x| x == &vec![1, 0, 1, 0]).unwrap());
        assert_eq!(c.nx[1][2][c.c[2].iter().position(|x| x == &vec![1, 3, 0]).unwrap()] as usize, c.c[3].iter().position(|x| x == &vec![3, 0]).unwrap());
        assert_eq!(c.nx[0][2][c.c[2].iter().position(|x| x == &vec![1, 3, 0]).unwrap()], NONE);
    }
    #[test]
    fn maxflow() {
        let b = |v: i64| BigInt::from(v);
        // sources (0,0):3, (1,1):2; receivers (0,0):1, (0,2):1, (1,1):2, (2,2):1; total need 5
        let sup = vec![(vec![0, 0], b(3)), (vec![1, 1], b(2))];
        let rec = vec![(vec![0, 0], b(1)), (vec![0, 2], b(1)), (vec![1, 1], b(2)), (vec![2, 2], b(1))];
        assert_eq!(maxflow_big(&sup, &rec).0, b(5));
        // negative: with no mass at (0, 0) only (1, 1) and (2, 2) can be fed: flow 3 < 5
        let sup2 = vec![(vec![0, 0], b(0)), (vec![1, 1], b(5))];
        assert_eq!(maxflow_big(&sup2, &rec).0, b(3));
    }
}
