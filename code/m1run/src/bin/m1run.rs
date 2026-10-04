//! The stored run of the lower model M1 (Proposition 13.3 and Proposition 15.1 of the paper):
//! stored rounded laws of every height 0..M-1, the top arrays at height M, and the seed masses.
//!
//! Usage: m1run V P W M QMAX RUNFILE MASSFILE
//!
//! RUNFILE (text, every value a natural number n standing for n / 2^W; a row has 4(V+1)
//! values, entry (a, g) at position 4a + g, a = 0..V, g = 0..3):
//!   M1RUN 1
//!   PARAMS <V> <P> <W> <M> <QMAX> sat
//!   RHO <h> <row>          rho*_h on (b, f), h = 0..M-1
//!   K <h> <f> <row>        K*_h(f -> .) on (a, f'), f = 0..3, after the RHO line of h
//!   WTIL <q> <row>         Wtil_q on (x, g) at the top height M, q = 2..QMAX
//!   END
//! Height 0 is Rhat_0, Khat_0 of Section 13 of the paper with q_L replaced by its limit 1/3,
//! rounded down; height h >= 1 is the recursion of Section 13 with p_L replaced by its limit 1/3,
//! on the stored height h - 1, rounded down (lib.rs). The formal proof shows that these values are,
//! off the bottom, below those of the recursion at L = 60 (FrogModel/D3/M1K/Height0.lean,
//! YSound.lean). Each stored law has its deficit at the bottom (0, 0) and sums to 2^W exactly.
//! Wtil_q is W_NNN(q) of the R closure at height M on the stored height M - 1, rounded down, with
//! nothing moved.
//!
//! MASSFILE (the masses W_k(x) of the seed of Proposition 15.1 (2)): "MASSV <M> <V>", then
//! "MASS <M> <k> <x> <n>" for k = 1..QMAX-1, x = 1..V, with n = sum over g of Wtil_{k+1}(x, g).

use m1run::*;
use std::io::Write;
use std::time::Instant;

fn row_str(l: &[u128]) -> String {
    l.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(" ")
}

fn with_deficit(mut l: Lanes, d: u128) -> Lanes {
    let s = sum(&l);
    assert!(s <= d);
    l[0] += d - s;
    l
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() != 8 {
        eprintln!("usage: m1run V P W M QMAX RUNFILE MASSFILE");
        std::process::exit(2);
    }
    let v: usize = a[1].parse().unwrap();
    let p: usize = a[2].parse().unwrap();
    let w: u32 = a[3].parse().unwrap();
    let m: usize = a[4].parse().unwrap();
    let qmax: usize = a[5].parse().unwrap();
    assert!(w <= 62 && v >= 1 && p >= 2 && m >= 1 && qmax >= 2 && qmax <= p);
    let par = Par { v, p, w, mode: Mode::Sat };
    let d = par.d();
    let mut f = std::io::BufWriter::new(std::fs::File::create(&a[6]).unwrap());
    writeln!(f, "M1RUN 1").unwrap();
    writeln!(f, "PARAMS {v} {p} {w} {m} {qmax} sat").unwrap();
    let t0 = Instant::now();
    let mut st = base_state_h0(&par);
    let put = |f: &mut std::io::BufWriter<std::fs::File>, h: usize, st: &State| {
        writeln!(f, "RHO {h} {}", row_str(&st.rho)).unwrap();
        for ff in 0..4 {
            writeln!(f, "K {h} {ff} {}", row_str(&st.k[ff])).unwrap();
        }
    };
    put(&mut f, 0, &st);
    println!("h 0 written");
    for h in 1..m {
        let th = Instant::now();
        let (rho, k, _) = step_raw(&par, &st);
        let def_rho = d - sum(&rho);
        let k2: [Lanes; 4] = core::array::from_fn(|i| with_deficit(k[i].clone(), d));
        st = State { rho: with_deficit(rho, d), k: k2 };
        put(&mut f, h, &st);
        println!("h {h} deficit_rho {def_rho} t {:.3}", th.elapsed().as_secs_f64());
    }
    let th = Instant::now();
    let (_, _, nnn) = step_raw(&par, &st);
    for q in 2..=qmax {
        writeln!(f, "WTIL {q} {}", row_str(&nnn[q])).unwrap();
    }
    writeln!(f, "END").unwrap();
    f.flush().unwrap();
    println!("top {m} written t {:.3}", th.elapsed().as_secs_f64());
    let mut g = std::io::BufWriter::new(std::fs::File::create(&a[7]).unwrap());
    writeln!(g, "MASSV {m} {v}").unwrap();
    for k in 1..qmax {
        let mut tot = 0u128;
        for x in 1..=v {
            let n: u128 = (0..4).map(|gg| nnn[k + 1][4 * x + gg]).sum();
            tot += n;
            writeln!(g, "MASS {m} {k} {x} {n}").unwrap();
        }
        assert!(tot <= d);
    }
    g.flush().unwrap();
    println!("# total {:.2} s", t0.elapsed().as_secs_f64());
}
